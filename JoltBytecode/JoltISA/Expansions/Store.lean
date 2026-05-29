import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Store-family Jolt expansion programs

NOTE: (for Ari) the triangle in examples such as
`.instr i <| .instr j <| .done RETIRE_SUCCESS` is Lean's left-facing pipeline
operator.  Here it lets the bytecode list read top-to-bottom: execute `i`, then
execute `j`, then retire.

These programs are the handwritten Jolt-ISA layer for the RV64 store inline
sequences.  They intentionally mirror `tracer/src/instruction/{sb,sh,sw}.rs`
rather than any proof-friendly reorganisation; proof files can introduce
blocks, but the program declarations should stay close to the Rust trace until
they are generated automatically.

Two details matter for stores:

* `VirtualAssertHalfwordAlignment` and `VirtualAssertWordAlignment` are the
  virtual assertions used by `SH` and `SW`. They return Sail's store/AMO
  alignment exception and stop the tail.
* Jolt's RV64 `LUI` helper writes the normalized immediate directly.  Thus
  `LUI v0, 0xff` writes `0xFF`, and `LUI v0, 0xffff` writes `0xFFFF`.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust store `v0`: effective address, then mask/shifted data depending on
the store width. -/
def storeV0 : VReg := inlineTmp0

/-- Rust store `v1`: aligned doubleword base address. -/
def storeV1 : VReg := inlineTmp1

/-- Rust store `v2`: loaded/spliced doubleword. -/
def storeV2 : VReg := inlineTmp2

/-- Rust store `v3`: shift amount or splice temporary. -/
def storeV3 : VReg := inlineTmp3

/-- Recursive `SLL` scratch while Rust store `v0..v3` guards are live. -/
def storeInlineTmp : VReg := inlineTmp4

/-- Rust store allocation layout on RV64: top-level `v0..v3`, then the
recursive shift helper's scratch while those guards are live. -/
theorem store_allocate_layout :
    allocateInstructionRegister [] = some (storeV0, [0]) ∧
    allocateInstructionRegister [0] = some (storeV1, [1, 0]) ∧
    allocateInstructionRegister [1, 0] = some (storeV2, [2, 1, 0]) ∧
    allocateInstructionRegister [2, 1, 0] = some (storeV3, [3, 2, 1, 0]) ∧
    allocateInstructionRegister [3, 2, 1, 0] =
      some (storeInlineTmp, [4, 3, 2, 1, 0]) := by
  decide

/-- RV64 Jolt expansion for `SB`, faithful to
`tracer/src/instruction/sb.rs::inline_sequence_64`. -/
def sbProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg storeV2) (.vreg storeV1) 0) <|
  slliBlock (.vreg storeV3) (.vreg storeV0) (3 : BitVec 6) <|
  .instr (.LUI (.vreg storeV0) (0xff : BitVec 64)) <|
  sllBlock (.vreg storeV0) (.vreg storeV0) (.vreg storeV3) storeInlineTmp <|
  sllBlock (.vreg storeV3) (.xreg rs2) (.vreg storeV3) storeInlineTmp <|
  .instr (.XOR (.vreg storeV3) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.AND (.vreg storeV3) (.vreg storeV3) (.vreg storeV0)) <|
  .instr (.XOR (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SH`, faithful to
`tracer/src/instruction/sh.rs::inline_sequence_64`. -/
def shProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg storeV2) (.vreg storeV1) 0) <|
  slliBlock (.vreg storeV3) (.vreg storeV0) (3 : BitVec 6) <|
  .instr (.LUI (.vreg storeV0) (0xffff : BitVec 64)) <|
  sllBlock (.vreg storeV0) (.vreg storeV0) (.vreg storeV3) storeInlineTmp <|
  sllBlock (.vreg storeV3) (.xreg rs2) (.vreg storeV3) storeInlineTmp <|
  .instr (.XOR (.vreg storeV3) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.AND (.vreg storeV3) (.vreg storeV3) (.vreg storeV0)) <|
  .instr (.XOR (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SW`, faithful to
`tracer/src/instruction/sw.rs::inline_sequence_64`. -/
def swProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg storeV2) (.vreg storeV1) 0) <|
  slliBlock (.vreg storeV0) (.vreg storeV0) (3 : BitVec 6) <|
  .instr (.ORI (.vreg storeV3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  srliBlock (.vreg storeV3) (.vreg storeV3) (32 : BitVec 6) <|
  sllBlock (.vreg storeV3) (.vreg storeV3) (.vreg storeV0) storeInlineTmp <|
  sllBlock (.vreg storeV0) (.xreg rs2) (.vreg storeV0) storeInlineTmp <|
  .instr (.XOR (.vreg storeV0) (.vreg storeV2) (.vreg storeV0)) <|
  .instr (.AND (.vreg storeV0) (.vreg storeV0) (.vreg storeV3)) <|
  .instr (.XOR (.vreg storeV2) (.vreg storeV2) (.vreg storeV0)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

end JoltISA
