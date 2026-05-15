import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Shared memory-access definitions

Shared type-level infrastructure used by both the load and store families:

* **Address abbrevs**: `load_effective_address`, `aligned_dword_addr`,
  `compute_aligned_dword_base_address` — how to compute the effective
  target address and its 8-aligned enclosing dword.
* **Assumption bundles**: `DwordLoadAssumptions` (aligned + translate +
  FlatPhysMem of the dword), `LoadReadAssumptions` (aligned + translate +
  FlatPhysMem for arbitrary width).
* **Properties of `aligned_dword_addr`**: that it's 8-aligned, doesn't
  overflow on `+7`, and satisfies the full `AlignedDwordAccess` bundle.
  Used by every load-family decomposed proof.
* **Pipeline-collapse theorems**: `aligned_dword_vmem_read_reduces` and
  `vreg_LD_run_of_dword_assumptions` — Sail's vmem-read / Jolt's vreg_LD
  under the dword-load assumptions.
-/

/-- Common aligned dword address used by the Jolt inline load sequences:
    compute the effective address, align it down to an 8-byte boundary,
    then use zero offset for the actual `LD`. -/
abbrev aligned_dword_addr (v : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (v + sign_extend (m := 64) imm) &&& sign_extend (m := 64) (-8 : BitVec 12)

/-- Generic effective address for memory instructions with a sign-extended
    12-bit immediate. -/
abbrev load_effective_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  val + sign_extend (m := 64) imm

/-- Generic aligned dword base address used by the Jolt inline memory
    sequences after computing the effective address. -/
abbrev compute_aligned_dword_base_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  load_effective_address val imm &&& (-8 : BitVec 64)

/-- The standard bundle of assumptions used to collapse Jolt's aligned dword
    load into a direct hashmap read. -/
structure DwordLoadAssumptions (addr : BitVec 64) (s : SailState) : Prop where
  aligned : AlignedDwordAccess addr
  translate : BareTranslation addr s
  phys : FlatPhysMem addr 8 s

/-- Generic bundle for non-dword Sail load-pipeline assumptions. Width-specific
    overflow side conditions, when needed, remain separate. -/
structure LoadReadAssumptions (addr : BitVec 64) (width : Nat) (s : SailState) : Prop where
  aligned : AlignedAccess addr width
  translate : BareTranslation addr s
  phys : FlatPhysMem addr width s

/-- `aligned_dword_addr` is just "effective address aligned down to 8 bytes". -/
theorem aligned_dword_addr_eq (v : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr v imm =
      (v + sign_extend (m := 64) imm) &&& (-8 : BitVec 64) := by
  unfold aligned_dword_addr
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  rw [h8]

-- ============================================================================
-- Properties of `aligned_dword_addr`
-- ============================================================================
-- These say: the Jolt inline-sequence base address (effective address with its
-- low 3 bits cleared) is 8-aligned, its `.toNat + 7` does not overflow 2^64,
-- and from those two facts it satisfies the full `AlignedDwordAccess` bundle.
-- Used by every load instruction's decomposed-program proof, so they live
-- next to the `aligned_dword_addr` definition rather than inside each
-- instruction file.

/-- The Jolt inline-sequence base address is naturally 8-aligned. -/
theorem aligned_dword_addr_aligns (val : BitVec 64) (imm : BitVec 12) :
    aligned_dword_addr val imm &&& 7 = 0 := by
  rw [aligned_dword_addr_eq]
  bv_decide

/-- An 8-aligned 64-bit address, viewed as a natural number, has no overflow
    when we add 7. -/
theorem aligned_addr_no_ovf_of_align (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    addr.toNat + 7 < 2 ^ 64 := by
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : BitVec.toNat (7 : BitVec 64) = 7 := by decide
    have h0 : BitVec.toNat (0 : BitVec 64) = 0 := by decide
    rw [h7, h0] at h
    rw [show (7 : Nat) = 2^3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- Specialisation of the previous lemma to the Jolt inline-sequence base
    address. -/
theorem aligned_dword_addr_no_ovf (val : BitVec 64) (imm : BitVec 12) :
    (aligned_dword_addr val imm).toNat + 7 < 2 ^ 64 :=
  aligned_addr_no_ovf_of_align _ (aligned_dword_addr_aligns val imm)

/-- The Jolt inline-sequence base address is a proper `AlignedDwordAccess`:
    misalignment check passes, split is trivial, address is 8-aligned, and
    `+7` doesn't overflow. -/
theorem aligned_dword_addr_is_aligned_dword_access (val : BitVec 64) (imm : BitVec 12) :
    AlignedDwordAccess (aligned_dword_addr val imm) := by
  refine
    { misalign := access_misaligned_8_aligned_false _ (aligned_dword_addr_aligns val imm)
      split := split_misaligned_aligned_8 _ (aligned_dword_addr_aligns val imm)
      align := aligned_dword_addr_aligns val imm
      no_ovf := aligned_dword_addr_no_ovf val imm }

/-- Transport the bundled dword-load assumptions across an address equality. -/
theorem DwordLoadAssumptions.of_eq {addr addr' : BitVec 64} {s : SailState}
    (h : addr = addr') :
    DwordLoadAssumptions addr s → DwordLoadAssumptions addr' s := by
  intro hd
  cases h
  exact hd

/-- Under the standard aligned-dword assumptions, Sail's virtual-memory read
    pipeline reduces to a direct dword read from the hash-map model. -/
theorem aligned_dword_vmem_read_reduces (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) (hd : DwordLoadAssumptions addr s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
      .ok (Ok (loaded_dword_at s addr)) s := by
  exact
    vmem_read_addr_dword_reduces addr s hcfg hd.aligned hd.translate hd.phys

/-- Specialised `vreg_LD` helper: if virtual source register `vs1` contains an
    aligned dword address satisfying the standard assumptions, then `vreg_LD`
    writes the corresponding `loaded_dword_at` value into `vd`. -/
theorem vreg_LD_run_of_dword_assumptions
    (vd vs1 : BitVec 7) (js : SailJoltState) (addr : BitVec 64)
    (hvs1 : js.vregs vs1 = addr) (hcfg : JoltConfig js.sail)
    (hd : DwordLoadAssumptions addr js.sail) :
    vreg_LD vd vs1 0 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then loaded_dword_at js.sail addr else js.vregs r } := by
  have hread :
      vmem_read_addr (Virtaddr (js.vregs vs1 + sign_extend (m := 64) (0 : BitVec 12))) 0 8
        (Load Data) false false false js.sail =
      .ok (Ok (loaded_dword_at js.sail addr)) js.sail := by
    have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
    rw [hvs1, h0]
    have haddr : addr + (0 : BitVec 64) = addr := by bv_decide
    rw [haddr]
    exact aligned_dword_vmem_read_reduces addr js.sail hcfg hd
  simpa using
    (vreg_LD_run_from_memory_read vd vs1 0 js (loaded_dword_at js.sail addr) hread)
