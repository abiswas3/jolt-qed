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
# Shared Jolt load-definition helpers

These helpers factor only the concrete inline-sequence code shared across the
Jolt load instructions. They deliberately do not try to abstract the proof
scripts or the pure bridge lemmas.

There are three recurring sequence families:

* byte loads (`LB`, `LBU`)
* halfword loads (`LH`, `LHU`)
* unsigned word loads (`LWU`)

`LW` is close, but its final `VirtualSignExtendWord` step changes the shape
enough that it is cleaner to leave its definition local for now.
-/

/-- Common aligned dword address used by the Jolt inline load sequences:
    compute the effective address, align it down to an 8-byte boundary,
    then use zero offset for the actual `LD`. -/
abbrev aligned_dword_addr (v : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (v + sign_extend (m := 64) imm &&& sign_extend (m := 64) (-8 : BitVec 12))
    + sign_extend (m := 64) (0 : BitVec 12)

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
  have h0 : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := by decide
  have h8 : sign_extend (m := 64) (-8 : BitVec 12) = (-8 : BitVec 64) := by decide
  rw [h0, h8]
  bv_decide

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
    (vreg_LD_run_of_read vd vs1 0 js (loaded_dword_at js.sail addr) hread)

/-- Shared body for the byte-load family. The caller supplies the final
    post-processing on the shifted dword: arithmetic right shift for `LB`,
    logical right shift for `LBU`. -/
def jolt_byte_load_family
    (imm : BitVec 12) (rs1 rd : regidx)
    (finish : BitVec 64 → BitVec 64) : JoltMonad ExecutionResult := do
  let rs1_val ← liftSail (rX_bits rs1)
  writeVReg 0 (rs1_val + sign_extend (m := 64) imm)
  let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
  match ← vreg_LD 1 1 0 with
  | .Retire_Success () =>
      let _ ← vreg_XORI 0 0 7
      let _ ← vreg_SLLI 0 0 3
      let _ ← vreg_SLL 1 1 0
      let v1 ← readVReg 1
      liftSail (wX_bits rd (finish v1))
      pure RETIRE_SUCCESS
  | other => pure other

/-- Shared body for the halfword-load family. The caller supplies the
    instruction-specific assertion message and the final post-processing:
    arithmetic right shift for `LH`, logical right shift for `LHU`. -/
def jolt_halfword_load_family
    (imm : BitVec 12) (rs1 rd : regidx) (msg : String)
    (finish : BitVec 64 → BitVec 64) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 1 ≠ 0 then
    throw (Error.Assertion msg)
  else do
    writeVReg 0 ea
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        let _ ← vreg_XORI 0 0 6
        let _ ← vreg_SLLI 0 0 3
        let _ ← vreg_SLL 1 1 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd (finish v1))
        pure RETIRE_SUCCESS
    | other => pure other

/-- Shared body for the unsigned word-load family (`LWU`). This uses the same
    dword-load + shift-left extraction pattern as byte/halfword loads, but
    with a 32-bit zero-extending result. -/
def jolt_word_unsigned_family
    (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "LWU: effective address not word-aligned")
  else do
    writeVReg 0 ea
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        let _ ← vreg_XORI 0 0 4
        let _ ← vreg_SLLI 0 0 3
        let _ ← vreg_SLL 1 1 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd (shift_bits_right v1 (32 : BitVec 6)))
        pure RETIRE_SUCCESS
    | other => pure other
