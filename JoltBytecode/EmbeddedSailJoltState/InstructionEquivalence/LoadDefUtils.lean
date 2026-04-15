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

