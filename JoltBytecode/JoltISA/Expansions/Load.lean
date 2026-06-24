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

/-- Rust source `rd = x0` rewrite destination for side-effecting load
expansions. -/
def loadDstFor (rd : regidx) : Dst :=
  sideEffectingRdZeroDst rd

/-- Rust load `v0`, shifted when `rd = x0` consumes the first temporary. -/
def loadV0For (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp1 else loadV0

/-- Rust load `v1`, shifted when `rd = x0` consumes the first temporary. -/
def loadV1For (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp2 else loadV1

/-- Recursive load scratch, shifted when `rd = x0` consumes the first
temporary. -/
def loadInlineTmpFor (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp3 else loadInlineTmp

/-- Rust's RV64 `LB::inline_sequence`. -/
def lbProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  .instr (.XORI (.vreg v0) (.vreg v0) 7) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSRAI dst (.vreg v1) (sraiBitmask (56 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LBU::inline_sequence`. -/
def lbuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  .instr (.XORI (.vreg v0) (.vreg v0) 7) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSRLI dst (.vreg v1) (srliBitmask (56 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LH::inline_sequence`. -/
def lhProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  .instr (.XORI (.vreg v0) (.vreg v0) 6) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSRAI dst (.vreg v1) (sraiBitmask (48 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LHU::inline_sequence`. -/
def lhuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.VirtualAssertHalfwordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  .instr (.XORI (.vreg v0) (.vreg v0) 6) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSRLI dst (.vreg v1) (srliBitmask (48 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LW::inline_sequence`. -/
def lwProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  srlBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSignExtendWord dst (.vreg v1)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `LWU::inline_sequence`. -/
def lwuProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  let v0 := loadV0For rd
  let v1 := loadV1For rd
  let tmp := loadInlineTmpFor rd
  let dst := loadDstFor rd
  .instr (.VirtualAssertWordAlignment rs1 imm (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg v0) (.xreg rs1) imm) <|
  .instr (.ANDI (.vreg v1) (.vreg v0) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg v1) (.vreg v1) 0) <|
  .instr (.XORI (.vreg v0) (.vreg v0) 4) <|
  slliBlock (.vreg v0) (.vreg v0) (3 : BitVec 6) <|
  sllBlock (.vreg v1) (.vreg v1) (.vreg v0) tmp <|
  .instr (.VirtualSRLI dst (.vreg v1) (srliBitmask (32 : BitVec 6))) <|
  .done RETIRE_SUCCESS

end JoltISA
