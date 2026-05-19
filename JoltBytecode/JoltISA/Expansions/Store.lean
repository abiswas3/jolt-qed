import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.Expansions.ALU

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

* `VirtualAssertStoreAlignment` is the virtual assertion used by `SH` and `SW`.  It
  returns Sail's store/AMO alignment exception and stops the tail.
* Jolt's RV64 `LUI` helper writes the normalized immediate directly.  Thus
  `LUI v0, 0xff` writes `0xFF`, and `LUI v0, 0xffff` writes `0xFFFF`.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- RV64 Jolt expansion for `SB`, faithful to
`tracer/src/instruction/sb.rs::inline_sequence_64`. -/
def sbProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg 2) (.vreg 1) 0) <|
  .instr (.VirtualMULI (.vreg 3) (.vreg 0) (8 : BitVec 64)) <|
  .instr (.LUI (.vreg 0) (0xff : BitVec 64)) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 3)) <|
  .instr (.MUL (.vreg 0) (.vreg 0) (.vreg 4)) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 3)) <|
  .instr (.MUL (.vreg 3) (.xreg rs2) (.vreg 4)) <|
  .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 3)) <|
  .instr (.AND (.vreg 3) (.vreg 3) (.vreg 0)) <|
  .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 3)) <|
  .instr (.SD (.vreg 1) (.vreg 2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SH`, faithful to
`tracer/src/instruction/sh.rs::inline_sequence_64`. -/
def shProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertHalfwordAlignment rs1 imm) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg 2) (.vreg 1) 0) <|
  .instr (.VirtualMULI (.vreg 3) (.vreg 0) (8 : BitVec 64)) <|
  .instr (.LUI (.vreg 0) (0xffff : BitVec 64)) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 3)) <|
  .instr (.MUL (.vreg 0) (.vreg 0) (.vreg 4)) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 3)) <|
  .instr (.MUL (.vreg 3) (.xreg rs2) (.vreg 4)) <|
  .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 3)) <|
  .instr (.AND (.vreg 3) (.vreg 3) (.vreg 0)) <|
  .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 3)) <|
  .instr (.SD (.vreg 1) (.vreg 2) 0) <|
  .done RETIRE_SUCCESS

/-- RV64 Jolt expansion for `SW`, faithful to
`tracer/src/instruction/sw.rs::inline_sequence_64`. -/
def swProgram (imm : BitVec 12) (rs2 rs1 : regidx) : Program :=
  .instr (.VirtualAssertWordAlignment rs1 imm) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg 2) (.vreg 1) 0) <|
  .instr (.VirtualMULI (.vreg 0) (.vreg 0) (8 : BitVec 64)) <|
  .instr (.ORI (.vreg 3) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  .instr (.VirtualSRLI (.vreg 3) (.vreg 3) (srliBitmask (32 : BitVec 6))) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 0)) <|
  .instr (.MUL (.vreg 3) (.vreg 3) (.vreg 4)) <|
  .instr (.VirtualPow2 (.vreg 4) (.vreg 0)) <|
  .instr (.MUL (.vreg 0) (.xreg rs2) (.vreg 4)) <|
  .instr (.XOR (.vreg 0) (.vreg 2) (.vreg 0)) <|
  .instr (.AND (.vreg 0) (.vreg 0) (.vreg 3)) <|
  .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 0)) <|
  .instr (.SD (.vreg 1) (.vreg 2) 0) <|
  .done RETIRE_SUCCESS

end JoltISA
