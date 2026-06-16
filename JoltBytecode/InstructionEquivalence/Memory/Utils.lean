import JoltBytecode.Derived
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# Memory utilities: direct hash-map byte assembly from `SailState.mem`.

These helpers skip Sail's vmem pipeline and read bytes straight from the
state's memory hash map. They are used to describe the intended effect of
memory-touching Jolt instructions in terms that are easy to reason about,
and are related back to Sail's pipeline via bridge theorems elsewhere.
-/

-- ============================================================================
-- Exact flat-memory predicates used by vmem helper lemmas
-- ============================================================================

/-- The bytes in `[addr, addr + width)` are present in Sail's finite memory map.

This is a local helper predicate for direct byte-level memory proofs. The
primitive public assumption is `Assumptions.DwordPresent`; sub-byte/word facts
are derived from it rather than assumed directly. -/
structure MemBytesPresent (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  present : ∀ k : Nat, k < width → s.mem.get? (addr.toNat + k) ≠ none

/-- Convenience spelling used by memory helper lemmas. -/
abbrev DwordBytesPresent (addr : BitVec 64) (s : SailState) : Prop :=
  MemBytesPresent addr 8 s

/-- Exact facts needed to reduce one ordinary `vmem_read_addr` data-load access
to a direct finite-memory read.

The fields mirror the Sail pipeline checks used by `vmem_read` after address
translation has reduced to the bare physical address: bytes are present in the
finite memory map, PMP permits the load, and the address is not readable MMIO. -/
structure FlatPhysMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  bytes : MemBytesPresent addr width s
  pmp : LoadPmpOk addr width s
  mmio : NotReadableMmio addr width s

/-- Exact facts needed to reduce one ordinary `vmem_write_addr` data-store
access to a direct finite-memory write.

Stores insert bytes into the finite memory map, so this does not require the
target bytes to be present before the write. Read-modify-write expansions use
`FlatLoadStoreMem`, because those proofs also read the original dword. -/
structure FlatStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  pmp : StorePmpOk addr width s
  mmio : NotWritableMmio addr width s

/-- Exact facts needed by Jolt read-modify-write expansions that first reduce a
`vmem_read_addr` dword load and later reduce a `vmem_write_addr` dword store at
the same flat-memory window.

Jolt store and `.W` AMO expansions load an enclosing dword, modify selected
lanes, then store the enclosing dword. The `bytes` field is the pre-write read
side; the PMP/MMIO fields cover both the load and store sides. -/
structure FlatLoadStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  bytes : MemBytesPresent addr width s
  load_pmp : LoadPmpOk addr width s
  store_pmp : StorePmpOk addr width s
  readable : NotReadableMmio addr width s
  writable : NotWritableMmio addr width s

namespace FlatLoadStoreMem

/-- Use the read half of a read-modify-write flat-memory window. -/
theorem toFlatPhysMem
    {addr : BitVec 64} {width : Nat} {s : SailState}
    (h : FlatLoadStoreMem addr width s) :
    FlatPhysMem addr width s :=
  { bytes := h.bytes
    pmp := h.load_pmp
    mmio := h.readable }

/-- Use the write half of a read-modify-write flat-memory window. -/
theorem toFlatStoreMem
    {addr : BitVec 64} {width : Nat} {s : SailState}
    (h : FlatLoadStoreMem addr width s) :
    FlatStoreMem addr width s :=
  { pmp := h.store_pmp
    mmio := h.writable }

end FlatLoadStoreMem

/-- Exact facts needed to reduce Sail's native AMO memory operation on the
ordinary flat-memory path.

The PMP check is the atomic PMP check, not separate load/store checks. The MMIO
predicates are still stated separately because the generated Sail memory
pipeline queries readable and writable MMIO paths independently. -/
structure FlatAtomicMem (op : amoop) (addr : BitVec 64) (width : Nat)
    (s : SailState) : Prop where
  bytes : MemBytesPresent addr width s
  pmp : AtomicPmpOk op addr width s
  readable : NotReadableMmio addr width s
  writable : NotWritableMmio addr width s

-- The 8-bit byte at a given vaddr. Direct hash-map lookup on `s.mem`.
-- WARNING: returns `0` when vaddr is not populated. Indistinguishable from
-- a legitimately-stored `0`. Callers must carry a populatedness hypothesis
-- (e.g. `MemBytesPresent`) to rule out the default branch.
def loaded_byte_at (s : SailState) (vaddr : BitVec 64) : BitVec 8 :=
  (s.mem.get? vaddr.toNat).getD 0

-- Explicit little-endian byte-assembly at standard RISC-V load widths.
-- Byte at `vaddr` occupies the low 8 bits; each successive byte stacks above.
-- No recursion, no dependent-type gymnastics — each definition is a plain
-- chain of `BitVec.append` (`++`) of `loaded_byte_at` calls.

def loaded_halfword_at (s : SailState) (vaddr : BitVec 64) : BitVec 16 :=
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

def loaded_word_at (s : SailState) (vaddr : BitVec 64) : BitVec 32 :=
  loaded_byte_at s (vaddr + 3) ++
  loaded_byte_at s (vaddr + 2) ++
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

def loaded_dword_at (s : SailState) (vaddr : BitVec 64) : BitVec 64 :=
  loaded_byte_at s (vaddr + 7) ++
  loaded_byte_at s (vaddr + 6) ++
  loaded_byte_at s (vaddr + 5) ++
  loaded_byte_at s (vaddr + 4) ++
  loaded_byte_at s (vaddr + 3) ++
  loaded_byte_at s (vaddr + 2) ++
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

-- ============================================================================
-- Reusable pipeline evidence
-- ============================================================================

/-- The access at `addr` of `width` bytes will not be split into multiple
    accesses by the Sail pipeline. This means:
    - The misalignment check passes (no trap on this access).
    - `split_misaligned` returns `(1, width)`: one access, full width.
    These hold when the address is naturally aligned or the platform
    allows misaligned access (`plat_enable_misaligned_access = true`). -/
structure AlignedAccess (addr : BitVec 64) (width : Nat) : Prop where
  misalign : access_causes_misaligned_exception (Virtaddr addr) width false = false
  split : split_misaligned (Virtaddr addr) width = (pure (1, width) : SailM (Int × Int))

/-- An 8-byte access that is naturally aligned with no address overflow. -/
structure AlignedDwordAccess (addr : BitVec 64) : Prop extends AlignedAccess addr 8 where
  align : addr &&& 7 = 0
  no_ovf : addr.toNat + 7 < 2 ^ 64

-- ============================================================================
-- Reusable pure alignment facts
-- ============================================================================
-- For each access width `w ∈ {4, 8}` we have three facts:
--   1. `access_misaligned_w_aligned_false` — if `addr` is `w`-aligned then the
--      Sail misalignment guard returns `false` (no exception raised).
--   2. `access_misaligned_w_unaligned_true` — if `addr` is NOT `w`-aligned then
--      the guard returns `true` (Sail raises the misalignment exception).
--   3. `split_misaligned_aligned_w` — if `addr` is `w`-aligned then Sail's
--      `split_misaligned` returns `pure (1, w)` (one access, full width).
-- These collapse the vmem pipeline into the clean "read all `w` bytes at once"
-- branch. Byte (width 1) is trivially aligned so doesn't need lemmas.

/-- Every address is aligned for a 1-byte access. -/
theorem access_misaligned_1_false (addr : BitVec 64) :
    access_causes_misaligned_exception (Virtaddr addr) 1 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  simp [Int.tmod, LeanRV64D.Functions.not]

/-- A 1-byte access never fragments. -/
theorem split_misaligned_1 (addr : BitVec 64) :
    split_misaligned (Virtaddr addr) 1 = (pure (1, 1) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  simp [Int.tmod, pure, EStateM.pure]

/-- The reusable aligned-access bundle for byte loads. -/
theorem aligned_access_1 (addr : BitVec 64) : AlignedAccess addr 1 := by
  exact
    { misalign := access_misaligned_1_false addr
      split := split_misaligned_1 addr }

/-- An 8-aligned address doesn't trigger the misalignment exception. -/
theorem access_misaligned_8_aligned_false (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 8 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-8-aligned address is not aligned according to Sail's virtual-address
    alignment predicate. -/
theorem is_aligned_vaddr_8_unaligned_false (addr : BitVec 64)
    (halign : addr &&& 7 ≠ 0) :
    is_aligned_vaddr (Virtaddr addr) 8 = false := by
  unfold is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7,
        hzero,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 8 ≠ 0 := by
    intro h0
    apply h_mod
    exact_mod_cast h0
  simp [Int.tmod, h_mod_int]

/-- A NON-8-aligned address triggers the misalignment exception for an
    8-byte access. -/
theorem access_misaligned_8_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 7 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 8 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7,
        hzero,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 8 ≠ 0 := by
    intro h0
    apply h_mod
    exact_mod_cast h0
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- An 8-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 8)` pair. -/
theorem split_misaligned_aligned_8 (addr : BitVec 64)
    (halign : addr &&& 7 = 0) :
    split_misaligned (Virtaddr addr) 8 = (pure (1, 8) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 8 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h7 : (7 : BitVec 64).toNat = 7 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h7, h0,
        show (7 : Nat) = 2^3 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

/-- A 4-aligned address (low 2 bits zero) doesn't trigger the misalignment
    exception for a 4-byte access. -/
theorem access_misaligned_4_aligned_false (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 4 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-4-aligned address triggers the misalignment exception for a 4-byte
    access (assuming the platform forbids misaligned access, which we have
    configured in `plat_enable_misaligned_access = false`). -/
theorem access_misaligned_4_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 3 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 4 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3,
        hzero,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 4 ≠ 0 := by
    intro h0
    apply h_mod
    have hdiv_int : (4 : Int) ∣ (addr.toNat : Int) :=
      Int.dvd_of_emod_eq_zero h0
    have hdiv_nat : 4 ∣ addr.toNat := by
      exact_mod_cast hdiv_int
    exact Nat.mod_eq_zero_of_dvd hdiv_nat
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- A 4-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 4)` pair. -/
theorem split_misaligned_aligned_4 (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    split_misaligned (Virtaddr addr) 4 = (pure (1, 4) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

/-- A 4-aligned 64-bit address has room for the full word window. -/
theorem aligned_word_addr_no_ovf (addr : BitVec 64)
    (halign : addr &&& 3 = 0) :
    addr.toNat + 3 < 2 ^ 64 := by
  have h_mod : addr.toNat % 4 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h3 : (3 : BitVec 64).toNat = 3 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h3, h0,
        show (3 : Nat) = 2^2 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- A 2-aligned 64-bit address has room for the full halfword window. -/
theorem aligned_halfword_addr_no_ovf (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    addr.toNat + 1 < 2 ^ 64 := by
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  have hlt : addr.toNat < 2 ^ 64 := addr.isLt
  omega

/-- A 2-aligned address (low 1 bit zero) doesn't trigger the misalignment
    exception for a 2-byte access. -/
theorem access_misaligned_2_aligned_false (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    access_causes_misaligned_exception (Virtaddr addr) 2 false = false := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, LeanRV64D.Functions.not]

/-- A NON-2-aligned address triggers the misalignment exception for a 2-byte
    access. -/
theorem access_misaligned_2_unaligned_true (addr : BitVec 64)
    (halign : addr &&& 1 ≠ 0) :
    access_causes_misaligned_exception (Virtaddr addr) 2 false = true := by
  unfold access_causes_misaligned_exception is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 ≠ 0 := by
    intro h0
    apply halign
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have hzero : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1,
        hzero,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        h0]
  have h_mod_int : (↑addr.toNat : Int) % 2 ≠ 0 := by
    intro h0
    apply h_mod
    have hdiv_int : (2 : Int) ∣ (addr.toNat : Int) :=
      Int.dvd_of_emod_eq_zero h0
    have hdiv_nat : 2 ∣ addr.toNat := by
      exact_mod_cast hdiv_int
    exact Nat.mod_eq_zero_of_dvd hdiv_nat
  simp [Int.tmod, h_mod_int, LeanRV64D.Functions.not, plat_enable_misaligned_access]

/-- A 2-aligned address doesn't fragment — `split_misaligned` yields the
    single-access `(1, 2)` pair. -/
theorem split_misaligned_aligned_2 (addr : BitVec 64)
    (halign : addr &&& 1 = 0) :
    split_misaligned (Virtaddr addr) 2 = (pure (1, 2) : SailM (Int × Int)) := by
  funext s
  unfold split_misaligned is_aligned_vaddr Sail.BitVec.toNatInt
  have h_mod : addr.toNat % 2 = 0 := by
    have h := congrArg BitVec.toNat halign
    rw [BitVec.toNat_and] at h
    have h1 : (1 : BitVec 64).toNat = 1 := by decide
    have h0 : (0 : BitVec 64).toNat = 0 := by decide
    rw [h1, h0,
        show (1 : Nat) = 2^1 - 1 from by norm_num,
        Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  simp [Int.tmod, h_mod, pure, EStateM.pure]

-- ============================================================================
-- Reusable EStateM / Sail plumbing lemmas
-- ============================================================================

@[simp] theorem liftM_pure_in_SailME {α} (x : α) :
    (liftM (pure x : SailM α) : SailME (Result (BitVec 64) ExecutionResult) α)
      = pure x := by
  rfl

theorem EStateM_bind_ok {ε σ α β : Type} {f : EStateM ε σ α} {g : α → EStateM ε σ β}
    {s : σ} {a : α} {s' : σ} (h : f s = .ok a s') :
    EStateM.bind f g s = g a s' := by
  simp [EStateM.bind, h]

theorem readReg_eq (r : Register) (s : SailState) (v : RegisterType r)
    (h : s.regs.get? r = some v) :
    (Sail.readReg r : SailM (RegisterType r)) s = .ok v s := by
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get, h]

theorem readByte_eq (n : Nat) (s : SailState) (v : BitVec 8)
    (h : s.mem.get? n = some v) :
    (PreSail.readByte n : SailM (BitVec 8)) s = .ok v s := by
  unfold PreSail.readByte
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get, h]

-- ============================================================================
-- Reusable direct-memory collapse lemmas
-- ============================================================================

theorem readBytes_8_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 8 s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    (PreSail.readBytes 8 addr.toNat : SailM _) s =
    .ok (loaded_dword_at s addr, none) s := by
  obtain ⟨b0, hb0'⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 0 (by omega))
  obtain ⟨b1, hb1⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 1 (by omega))
  obtain ⟨b2, hb2⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 2 (by omega))
  obtain ⟨b3, hb3⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 3 (by omega))
  obtain ⟨b4, hb4⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 4 (by omega))
  obtain ⟨b5, hb5⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 5 (by omega))
  obtain ⟨b6, hb6⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 6 (by omega))
  obtain ⟨b7, hb7⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 7 (by omega))
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  unfold loaded_dword_at loaded_byte_at
  simp only [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 2).toNat = addr.toNat + 2 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 3).toNat = addr.toNat + 3 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 4).toNat = addr.toNat + 4 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 5).toNat = addr.toNat + 5 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 6).toNat = addr.toNat + 6 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 7).toNat = addr.toNat + 7 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.getD]
  rfl

theorem readBytes_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 1 s) :
    (PreSail.readBytes 1 addr.toNat : SailM _) s =
    .ok (loaded_byte_at s addr, none) s := by
  obtain ⟨b0, hb0'⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 0 (by omega))
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0]
  unfold loaded_byte_at
  simp only [hb0, Option.getD]

theorem readBytes_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 2 s)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64) :
    (PreSail.readBytes 2 addr.toNat : SailM _) s =
    .ok (loaded_halfword_at s addr, none) s := by
  obtain ⟨b0, hb0'⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 0 (by omega))
  obtain ⟨b1, hb1⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 1 (by omega))
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1]
  unfold loaded_halfword_at loaded_byte_at
  simp only [hb0, hb1,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.getD]
  rfl

theorem readBytes_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 4 s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64) :
    (PreSail.readBytes 4 addr.toNat : SailM _) s =
    .ok (loaded_word_at s addr, none) s := by
  obtain ⟨b0, hb0'⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 0 (by omega))
  obtain ⟨b1, hb1⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 1 (by omega))
  obtain ⟨b2, hb2⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 2 (by omega))
  obtain ⟨b3, hb3⟩ := Option.ne_none_iff_exists'.mp (hbytes.present 3 (by omega))
  have hb0 : s.mem.get? addr.toNat = some b0 := by simpa using hb0'
  simp only [PreSail.readBytes, PreSail.readByte,
             bind, EStateM.bind, pure, EStateM.pure,
             MonadStateOf.get, EStateM.get, getThe, get,
             hb0, hb1, hb2, hb3]
  unfold loaded_word_at loaded_byte_at
  simp only [hb0, hb1, hb2, hb3,
             show (addr + 1).toNat = addr.toNat + 1 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 2).toNat = addr.toNat + 2 from by apply BitVec.toNat_add_of_lt; simp; omega,
             show (addr + 3).toNat = addr.toNat + 3 from by apply BitVec.toNat_add_of_lt; simp; omega,
             Option.getD]
  rfl

theorem read_ram_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 1 s) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 1 false s =
    .ok (loaded_byte_at s addr, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_1_eq_loaded_byte addr s hbytes]
  simp [EStateM.pure]

theorem read_ram_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 2 s)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 2 false s =
    .ok (loaded_halfword_at s addr, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_2_eq_loaded_halfword addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem read_ram_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 4 s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 4 false s =
    .ok (loaded_word_at s addr, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_4_eq_loaded_word addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem checked_mem_read_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 1 s)
    (hfm : FlatPhysMem addr 1 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 1 false false false false s =
    .ok (Ok (loaded_byte_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.mmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_1_eq_loaded_byte addr s hbytes]

theorem checked_mem_read_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 2 s)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64)
    (hfm : FlatPhysMem addr 2 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 2 false false false false s =
    .ok (Ok (loaded_halfword_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.mmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_2_eq_loaded_halfword addr s hbytes h_no_ovf]

theorem checked_mem_read_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hbytes : MemBytesPresent addr 4 s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hfm : FlatPhysMem addr 4 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 4 false false false false s =
    .ok (Ok (loaded_word_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.mmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_4_eq_loaded_word addr s hbytes h_no_ovf]

theorem mem_read_1_eq_loaded_byte (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (hfm : FlatPhysMem addr 1 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 1 false false false s =
    .ok (Ok (loaded_byte_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_1_eq_loaded_byte addr s hfm.bytes hfm]

theorem mem_read_2_eq_loaded_halfword (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 1 < 2 ^ 64)
    (hfm : FlatPhysMem addr 2 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 2 false false false s =
    .ok (Ok (loaded_halfword_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_2_eq_loaded_halfword addr s hfm.bytes h_no_ovf hfm]

theorem mem_read_4_eq_loaded_word (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 3 < 2 ^ 64)
    (hfm : FlatPhysMem addr 4 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 4 false false false s =
    .ok (Ok (loaded_word_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_4_eq_loaded_word addr s hfm.bytes h_no_ovf hfm]

theorem vmem_read_addr_byte_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 1)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 1 false false false s =
        .ok (Ok (loaded_byte_at s addr)) s) :
    vmem_read_addr (Virtaddr addr) offset 1 (Load Data) false false false s =
    .ok (Ok (loaded_byte_at s addr)) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_load_data_of_joltConfig addr s hcfg
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  bv_decide

theorem vmem_read_byte_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 1)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 1 false false false s =
        .ok (Ok (loaded_byte_at s (v + sign_extend (m := 64) imm))) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 1 (Load Data) false false false s =
    .ok (Ok (loaded_byte_at s (v + sign_extend (m := 64) imm))) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_byte_bridge _ _ s hcfg ha h_mem]

theorem vmem_read_addr_halfword_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 2)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 2 false false false s =
        .ok (Ok (loaded_halfword_at s addr)) s) :
    vmem_read_addr (Virtaddr addr) offset 2 (Load Data) false false false s =
    .ok (Ok (loaded_halfword_at s addr)) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_load_data_of_joltConfig addr s hcfg
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  bv_decide

theorem vmem_read_addr_word_bridge (addr : BitVec 64) (offset : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 4)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 4 false false false s =
        .ok (Ok (loaded_word_at s addr)) s) :
    vmem_read_addr (Virtaddr addr) offset 4 (Load Data) false false false s =
    .ok (Ok (loaded_word_at s addr)) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_load_data_of_joltConfig addr s hcfg
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift, ExceptT.map, ExceptT.instMonadLift,
        MonadLift.monadLift, SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        Except.ok, Except.error,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        liftM, monadLift, Functor.map,
        ha.split, htranslate, h_mem]
  bv_decide

theorem read_ram_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : DwordBytesPresent addr s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    LeanRV64D.Functions.read_ram read_kind.Read_plain (physaddr.Physaddr addr) 8 false s =
    .ok (loaded_dword_at s addr, default_meta) s := by
  dsimp [LeanRV64D.Functions.read_ram,
         Sail.ConcurrencyInterfaceV1.sail_mem_read,
         PreSail.ConcurrencyInterfaceV1.sail_mem_read,
         default_meta]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [readBytes_8_eq_loaded_dword addr s hbytes h_no_ovf]
  simp [EStateM.pure]

theorem checked_mem_read_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hbytes : DwordBytesPresent addr s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hfm : FlatPhysMem addr 8 s) :
    checked_mem_read (Load Data) Privilege.Machine (physaddr.Physaddr addr) 8 false false false false s =
    .ok (Ok (loaded_dword_at s addr, default_meta)) s := by
  unfold checked_mem_read
  simp only [bind, EStateM.bind, pure, EStateM.pure, hfm.pmp, hfm.mmio,
             Bool.false_eq_true, if_false]
  unfold read_kind_of_flags
  simp only [pure, EStateM.pure]
  rw [read_ram_eq_loaded_dword addr s hbytes h_no_ovf]

theorem mem_read_eq_loaded_dword (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (hfm : FlatPhysMem addr 8 s) :
    mem_read (Load Data) (physaddr.Physaddr addr) 8 false false false s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  obtain ⟨mval, h_ms_regs, h_mprv⟩ := hcfg.mstatus_mprv.value
  have h_ms_read := readReg_eq Register.mstatus s mval h_ms_regs
  have h_priv := readReg_eq Register.cur_privilege s Privilege.Machine hcfg.cur_privilege.value
  unfold mem_read mem_read_priv
  simp only [bind, EStateM.bind, pure, EStateM.pure, h_ms_read, h_priv]
  unfold effectivePrivilege
  simp only [h_mprv, bne, BEq.beq]
  unfold mem_read_priv_meta
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false]
  simp (config := { decide := true }) only [ite_false, EStateM.pure, MemoryOpResult_drop_meta]
  rw [checked_mem_read_eq_loaded_dword addr s hfm.bytes h_no_ovf hfm]

theorem vmem_read_addr_pipeline_bridge (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s) (ha : AlignedAccess addr 8)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr addr) 8 false false false s =
        .ok (Ok (loaded_dword_at s addr)) s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
    .ok (Ok (loaded_dword_at s addr)) s := by
  unfold vmem_read_addr
  simp only [ha.misalign, Bool.false_eq_true, if_false]
  unfold SailME.run PreSail.PreSailME.run
  have htranslate := translateAddr_load_data_of_joltConfig addr s hcfg
  simp [ExceptT.mk, ExceptT.run,
        SailME.throw, PreSail.PreSailME.throw, MonadExceptOf.throw,
        misaligned_order, sys_misaligned_order_decreasing,
        bits_of_virtaddr, Sail.assert, PreSail.assert,
        untilFuelM, untilFuelM.go, zeros, BitVec.zero, BitVec.addInt,
        ha.split]
  simp only [liftM, monadLift, MonadLift.monadLift,
             ExceptT.lift, ExceptT.mk,
             bind, EStateM.bind, EStateM.map,
             Functor.map, htranslate, h_mem,
             ExceptT.bind, ExceptT.bindCont, ExceptT.map,
             Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  simp [pure, EStateM.pure, ExceptT.pure, ExceptT.mk]

theorem vmem_read_addr_dword_reduces (addr : BitVec 64) (s : SailState)
    (hcfg : JoltConfig s)
    (hda : AlignedDwordAccess addr) (hfm : FlatPhysMem addr 8 s) :
    vmem_read_addr (Virtaddr addr) 0 8 (Load Data) false false false s =
    .ok (Ok (loaded_dword_at s addr)) s :=
  vmem_read_addr_pipeline_bridge addr s hcfg hda.toAlignedAccess
    (mem_read_eq_loaded_dword addr s hcfg hda.no_ovf hfm)

theorem vmem_read_word_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 4)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 4 false false false s =
        .ok (Ok (loaded_word_at s (v + sign_extend (m := 64) imm))) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 4 (Load Data) false false false s =
    .ok (Ok (loaded_word_at s (v + sign_extend (m := 64) imm))) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_word_bridge _ _ s hcfg ha h_mem]

theorem vmem_read_halfword_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState) (hcfg : JoltConfig s)
    (v : BitVec 64) (hrx : rX_bits rs1 s = .ok v s)
    (ha : AlignedAccess (v + sign_extend (m := 64) imm) 2)
    (h_mem :
      mem_read (Load Data) (physaddr.Physaddr (v + sign_extend (m := 64) imm)) 2 false false false s =
        .ok (Ok (loaded_halfword_at s (v + sign_extend (m := 64) imm))) s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 2 (Load Data) false false false s =
    .ok (Ok (loaded_halfword_at s (v + sign_extend (m := 64) imm))) s := by
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
        ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
        ExceptT.pure, ExceptT.lift,
        MonadLift.monadLift, liftM, monadLift, Functor.map,
        ext_data_get_addr, hrx,
        vmem_read_addr_halfword_bridge _ _ s hcfg ha h_mem]

end
