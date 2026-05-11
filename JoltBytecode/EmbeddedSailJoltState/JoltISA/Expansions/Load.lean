import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics

/-!
# Load-family Jolt expansion programs

NOTE: (for ari) The `<|` operator is just low-precedence function application.
So `.instr A <| .instr B <| .done RETIRE_SUCCESS` means
`.instr A (.instr B (.done RETIRE_SUCCESS))`.  We use it so the nested
`Program.instr` tree reads top-to-bottom like the Rust bytecode sequence.

These definitions are the Jolt-ISA data representation of the Rust inline
sequences for RV64 loads.  They intentionally expose both kinds of early exit:

* `AssertLoadAlign` returns the load-address-alignment exception before the
  memory read when the effective address is misaligned.
* `LD` may return a memory exception; `Program.instr` then prevents the
  extraction/writeback tail from running.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's RV64 `LB::inline_sequence`. -/
def lbProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.XORI (.vreg 0) (.vreg 0) 7) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
  .instr (.SRAI (.xreg rd) (.vreg 1) (56 : BitVec 6)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LBU::inline_sequence`. -/
def lbuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.XORI (.vreg 0) (.vreg 0) 7) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
  .instr (.SRLI (.xreg rd) (.vreg 1) (56 : BitVec 6)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LH::inline_sequence`. -/
def lhProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.AssertLoadAlign rs1 imm (1 : BitVec 64)) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.XORI (.vreg 0) (.vreg 0) 6) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
  .instr (.SRAI (.xreg rd) (.vreg 1) (48 : BitVec 6)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LHU::inline_sequence`. -/
def lhuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.AssertLoadAlign rs1 imm (1 : BitVec 64)) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.XORI (.vreg 0) (.vreg 0) 6) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
  .instr (.SRLI (.xreg rd) (.vreg 1) (48 : BitVec 6)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LW::inline_sequence`. -/
def lwProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.AssertLoadAlign rs1 imm (3 : BitVec 64)) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SRL (.xreg rd) (.vreg 1) (.vreg 0)) <|
  .instr (.SExtW (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LWU::inline_sequence`. -/
def lwuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.AssertLoadAlign rs1 imm (3 : BitVec 64)) <|
  .instr (.ADDI (.vreg 0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) (-8 : BitVec 12)) <|
  .instr (.LD 1 1 0) <|
  .instr (.XORI (.vreg 0) (.vreg 0) 4) <|
  .instr (.SLLI (.vreg 0) (.vreg 0) 3) <|
  .instr (.SLL (.vreg 1) (.vreg 1) (.vreg 0)) <|
  .instr (.SRLI (.xreg rd) (.vreg 1) (32 : BitVec 6)) <|
  .done RETIRE_SUCCESS

end JoltISA
