import JoltBytecode.JoltISA.Instruction
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
* `VirtualWindowMask*` and `VirtualShiftData*` select the target lane before
  `ANDN` clears it and `ADD` inserts the shifted store value.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust store `v0`: effective address. -/
def storeV0 : VReg := inlineTmp0

/-- Rust store `v1`: aligned doubleword base address. -/
def storeV1 : VReg := inlineTmp1

/-- Rust store `v2`: loaded/spliced doubleword. -/
def storeV2 : VReg := inlineTmp2

/-- Rust store `v3`: window mask, then shifted store data. -/
def storeV3 : VReg := inlineTmp3

/-- RV64 Jolt expansion for `SB`, faithful to
`tracer/src/instruction/sb.rs::inline_sequence_64`. -/
def sbProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg storeV2) (.vreg storeV1) 0) <|
  .instr (.VirtualWindowMaskB (.vreg storeV3) (.vreg storeV0) 0) <|
  .instr (.ANDN (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.VirtualShiftDataB (.vreg storeV3) (.xreg rs2) (.vreg storeV0)) <|
  .instr (.ADD (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SH`, faithful to
`tracer/src/instruction/sh.rs::inline_sequence_64`. -/
def shProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg storeV2) (.vreg storeV1) 0) <|
  .instr (.VirtualWindowMaskH (.vreg storeV3) (.vreg storeV0) 0) <|
  .instr (.ANDN (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.VirtualShiftDataH (.vreg storeV3) (.xreg rs2) (.vreg storeV0)) <|
  .instr (.ADD (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SW`, faithful to
`tracer/src/instruction/sw.rs::inline_sequence_64`. -/
def swProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ADDI (.vreg storeV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg storeV1) (.vreg storeV0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg storeV2) (.vreg storeV1) 0) <|
  .instr (.VirtualWindowMaskW (.vreg storeV3) (.vreg storeV0) 0) <|
  .instr (.ANDN (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.VirtualShiftDataW (.vreg storeV3) (.xreg rs2) (.vreg storeV0)) <|
  .instr (.ADD (.vreg storeV2) (.vreg storeV2) (.vreg storeV3)) <|
  .instr (.SD (.vreg storeV1) (.vreg storeV2) 0) <|
  .done RETIRE_SUCCESS

end JoltISA
