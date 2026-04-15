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
# LW: Jolt load-word (signed) decomposition

From `tracer/src/instruction/lw.rs::inline_sequence_64`:

    VirtualAssertWordAlignment rs1, imm
    ADDI  v0, rs1, imm
    ANDI  rd, v0, -8
    LD    rd, rd, 0
    SLLI  v0, v0, 3
    SRL   rd, rd, v0
    VirtualSignExtendWord rd, rd, 0
-/

def jolt_lw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "LW: effective address not word-aligned")
  else do
    -- ADDI v0, rs1, imm
    writeVReg 0 ea
    -- ANDI rd, v0, -8  encoded via virtual register 1 for the dword address
    let v0 ← readVReg 0
    writeVReg 1 (v0 &&& (-8 : BitVec 64))
    -- LD rd, rd, 0  encoded as a dword load into virtual register 1
    match ← vreg_LD 1 1 0 with
    | .Retire_Success () =>
        -- SLLI v0, v0, 3
        let _ ← vreg_SLLI 0 0 3
        -- SRL rd, rd, v0
        let _ ← vreg_SRL 1 1 0
        -- VirtualSignExtendWord rd, rd, 0
        let v1 ← readVReg 1
        liftSail (wX_bits rd v1)
        jolt_virtual_sign_extend_word rd
        pure RETIRE_SUCCESS
    | other => pure other
