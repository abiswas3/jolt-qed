import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Load-family Jolt expansion programs

NOTE: (for ari) The `<|` operator is just low-precedence function application.
So `.instr A <| .instr B <| .done RETIRE_SUCCESS` means
`.instr A (.instr B (.done RETIRE_SUCCESS))`.  We use it so the nested
`Program.instr` tree reads top-to-bottom like the Rust bytecode sequence.

These definitions are the Jolt-ISA data representation of the Rust inline
sequences for RV64 loads.  They intentionally expose both kinds of early exit:

* `VirtualAssertHalfwordAlignment` and `VirtualAssertWordAlignment` return the
  load-address-alignment exception before the memory read when the effective
  address is misaligned.
* `LD` may return a memory exception; `Program.instr` then prevents the
  extraction/writeback tail from running.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust load `v0`: effective address, then byte/halfword/word shift amount. -/
def loadV0 : VReg := inlineTmp0

/-- Rust load `v1`: aligned doubleword address, then loaded/shifted doubleword. -/
def loadV1 : VReg := inlineTmp1

/-- Recursive `SLL`/`SRL` scratch while Rust load `v0,v1` guards are live. -/
def loadInlineTmp : VReg := inlineTmp2

/-- Rust's RV64 `LB::inline_sequence`. -/
def lbProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  .instr (.XORI (.vreg loadV0) (.vreg loadV0) 7) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  sllBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSRAI (.xreg rd) (.vreg loadV1) (sraiBitmask (56 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LBU::inline_sequence`. -/
def lbuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  .instr (.XORI (.vreg loadV0) (.vreg loadV0) 7) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  sllBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSRLI (.xreg rd) (.vreg loadV1) (srliBitmask (56 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LH::inline_sequence`. -/
def lhProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  .instr (.XORI (.vreg loadV0) (.vreg loadV0) 6) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  sllBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSRAI (.xreg rd) (.vreg loadV1) (sraiBitmask (48 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LHU::inline_sequence`. -/
def lhuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  .instr (.XORI (.vreg loadV0) (.vreg loadV0) 6) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  sllBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSRLI (.xreg rd) (.vreg loadV1) (srliBitmask (48 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LW::inline_sequence`. -/
def lwProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  srlBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg loadV1)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LWU::inline_sequence`. -/
def lwuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg loadV0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg loadV1) (.vreg loadV0) (-8 : BitVec 12)) <|
  .instr (.LD (.vreg loadV1) (.vreg loadV1) 0) <|
  .instr (.XORI (.vreg loadV0) (.vreg loadV0) 4) <|
  slliBlock (.vreg loadV0) (.vreg loadV0) (3 : BitVec 6) <|
  sllBlock (.vreg loadV1) (.vreg loadV1) (.vreg loadV0) loadInlineTmp <|
  .instr (.VirtualSRLI (.xreg rd) (.vreg loadV1) (srliBitmask (32 : BitVec 6))) <|
  .done RETIRE_SUCCESS

end JoltISA
