import LeanRV64D.InstsEnd
import JoltBytecode.JoltISA.Execution
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.Expansions.LoadReserved
import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Addw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Rem
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remu
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remw

/-!
# RISC-V Instructions

This file records the operand-bearing guest RISC-V instruction universe accepted
by Jolt's Rust `RV64IMAC_JOLT` source profile.

Rust is the source of truth for which guest opcodes Jolt accepts; the RISC-V ISA
docs are cited for the meaning of those opcodes.
-/

open Sail PreSail

/-- A CSR address is the 12-bit `csr` field used by Zicsr instructions. -/
abbrev CsrAddr := BitVec 12

/-- `fm`, `pred`, and `succ` are 4-bit FENCE fields. -/
abbrev FenceField := BitVec 4

/-- Guest RISC-V instruction constructors with operands.

Sources:
* Jolt accepted source instruction list:
  `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-riscv/src/lib.rs`,
  `for_each_instruction_kind!`.
* Jolt source extension assignment:
  `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-riscv/src/kind.rs`,
  `source_extension_for_marker`.
* RV32I base integer instructions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html
* RV64I base integer additions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html
* M extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html
* A extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html
* Zicsr extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html
* MRET privileged instruction listing:
  https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html
-/
inductive RiscvInstruction where
  /- RV32I base integer instruction set, inherited by RV64I.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html -/
  | LUI (rd : regidx) (imm : BitVec 20)
  | AUIPC (rd : regidx) (imm : BitVec 20)
  | JAL (rd : regidx) (imm : BitVec 21)
  | JALR (rd rs1 : regidx) (imm : BitVec 12)
  | BEQ (rs1 rs2 : regidx) (imm : BitVec 13)
  | BNE (rs1 rs2 : regidx) (imm : BitVec 13)
  | BLT (rs1 rs2 : regidx) (imm : BitVec 13)
  | BGE (rs1 rs2 : regidx) (imm : BitVec 13)
  | BLTU (rs1 rs2 : regidx) (imm : BitVec 13)
  | BGEU (rs1 rs2 : regidx) (imm : BitVec 13)
  | LB (rd rs1 : regidx) (imm : BitVec 12)
  | LH (rd rs1 : regidx) (imm : BitVec 12)
  | LW (rd rs1 : regidx) (imm : BitVec 12)
  | LBU (rd rs1 : regidx) (imm : BitVec 12)
  | LHU (rd rs1 : regidx) (imm : BitVec 12)
  | SB (rs2 rs1 : regidx) (imm : BitVec 12)
  | SH (rs2 rs1 : regidx) (imm : BitVec 12)
  | SW (rs2 rs1 : regidx) (imm : BitVec 12)
  | ADDI (rd rs1 : regidx) (imm : BitVec 12)
  | SLTI (rd rs1 : regidx) (imm : BitVec 12)
  | SLTIU (rd rs1 : regidx) (imm : BitVec 12)
  | XORI (rd rs1 : regidx) (imm : BitVec 12)
  | ORI (rd rs1 : regidx) (imm : BitVec 12)
  | ANDI (rd rs1 : regidx) (imm : BitVec 12)
  | SLLI (rd rs1 : regidx) (shamt : BitVec 6)
  | SRLI (rd rs1 : regidx) (shamt : BitVec 6)
  | SRAI (rd rs1 : regidx) (shamt : BitVec 6)
  | ADD (rd rs1 rs2 : regidx)
  | SUB (rd rs1 rs2 : regidx)
  | SLL (rd rs1 rs2 : regidx)
  | SLT (rd rs1 rs2 : regidx)
  | SLTU (rd rs1 rs2 : regidx)
  | XOR (rd rs1 rs2 : regidx)
  | SRL (rd rs1 rs2 : regidx)
  | SRA (rd rs1 rs2 : regidx)
  | OR (rd rs1 rs2 : regidx)
  | AND (rd rs1 rs2 : regidx)
  | FENCE (rd rs1 : regidx) (fm pred succ : FenceField)
  | ECALL
  | EBREAK

  /- RV64I base integer additions.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html -/
  | LWU (rd rs1 : regidx) (imm : BitVec 12)
  | LD (rd rs1 : regidx) (imm : BitVec 12)
  | SD (rs2 rs1 : regidx) (imm : BitVec 12)
  | ADDIW (rd rs1 : regidx) (imm : BitVec 12)
  | SLLIW (rd rs1 : regidx) (shamt : BitVec 5)
  | SRLIW (rd rs1 : regidx) (shamt : BitVec 5)
  | SRAIW (rd rs1 : regidx) (shamt : BitVec 5)
  | ADDW (rd rs1 rs2 : regidx)
  | SUBW (rd rs1 rs2 : regidx)
  | SLLW (rd rs1 rs2 : regidx)
  | SRLW (rd rs1 rs2 : regidx)
  | SRAW (rd rs1 rs2 : regidx)

  /- M extension for integer multiplication and division.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html -/
  | MUL (rd rs1 rs2 : regidx)
  | MULH (rd rs1 rs2 : regidx)
  | MULHU (rd rs1 rs2 : regidx)
  | MULHSU (rd rs1 rs2 : regidx)
  | DIV (rd rs1 rs2 : regidx) (quotient remAbs : BitVec 64)
  | DIVU (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | REM (rd rs1 rs2 : regidx) (quotient remAbs : BitVec 64)
  | REMU (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | MULW (rd rs1 rs2 : regidx)
  | DIVW (rd rs1 rs2 : regidx) (quotient remAbs : BitVec 64)
  | DIVUW (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | REMW (rd rs1 rs2 : regidx) (quotient remAbs : BitVec 64)
  | REMUW (rd rs1 rs2 : regidx) (quotient : BitVec 64)

  /- A extension for atomic instructions. The `aq` and `rl` operands are the
     acquire and release bits in the atomic instruction encoding.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html -/
  | LR_W (rd rs1 : regidx) (aq rl : Bool)
  | SC_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOSWAP_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOADD_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOXOR_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOAND_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOOR_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMIN_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAX_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMINU_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAXU_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | LR_D (rd rs1 : regidx) (aq rl : Bool)
  | SC_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOSWAP_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOADD_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOXOR_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOAND_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOOR_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMIN_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAX_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMINU_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAXU_D (rd rs1 rs2 : regidx) (aq rl : Bool)

  /- Jolt-supported Zicsr source instructions.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html -/
  | CSRRW (rd : regidx) (csr : CsrAddr) (rs1 : regidx)
  | CSRRS (rd : regidx) (csr : CsrAddr) (rs1 : regidx)

  /- Jolt-supported RvPrivileged source instruction.
     Source: https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html -/
  | MRET
  deriving Repr

namespace RiscvInstruction

abbrev SailExecution := SailM ExecutionResult

private def pureResult (result : ExecutionResult) : SailExecution :=
  pure result

private def mulLow : mul_op :=
  { result_part := VectorHalf.Low
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

private def mulHighSigned : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

private def mulHighSignedUnsigned : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Unsigned }

private def mulHighUnsigned : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Unsigned
    signed_rs2 := Signedness.Unsigned }

/-- Generated LeanRV64D/Sail execution for the instruction, when this Sail model
has a direct execution entry for that constructor. -/
noncomputable def sailExecution : RiscvInstruction → Option SailExecution
  | .LUI rd imm => some (LeanRV64D.Functions.execute_UTYPE imm rd uop.LUI)
  | .AUIPC rd imm => some (LeanRV64D.Functions.execute_UTYPE imm rd uop.AUIPC)
  | .JAL rd imm => some (LeanRV64D.Functions.execute_JAL imm rd)
  | .JALR rd rs1 imm => some (LeanRV64D.Functions.execute_JALR imm rs1 rd)
  | .BEQ rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BEQ)
  | .BNE rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BNE)
  | .BLT rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BLT)
  | .BGE rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BGE)
  | .BLTU rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BLTU)
  | .BGEU rs1 rs2 imm => some (LeanRV64D.Functions.execute_BTYPE imm rs2 rs1 bop.BGEU)
  | .LB rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd false 1)
  | .LH rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd false 2)
  | .LW rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd false 4)
  | .LBU rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd true 1)
  | .LHU rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd true 2)
  | .SB rs2 rs1 imm => some (LeanRV64D.Functions.execute_STORE imm rs2 rs1 1)
  | .SH rs2 rs1 imm => some (LeanRV64D.Functions.execute_STORE imm rs2 rs1 2)
  | .SW rs2 rs1 imm => some (LeanRV64D.Functions.execute_STORE imm rs2 rs1 4)
  | .ADDI rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.ADDI)
  | .SLTI rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.SLTI)
  | .SLTIU rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.SLTIU)
  | .XORI rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.XORI)
  | .ORI rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.ORI)
  | .ANDI rd rs1 imm => some (LeanRV64D.Functions.execute_ITYPE imm rs1 rd iop.ANDI)
  | .SLLI rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIOP shamt rs1 rd sop.SLLI)
  | .SRLI rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIOP shamt rs1 rd sop.SRLI)
  | .SRAI rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIOP shamt rs1 rd sop.SRAI)
  | .ADD rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.ADD)
  | .SUB rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SUB)
  | .SLL rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SLL)
  | .SLT rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SLT)
  | .SLTU rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SLTU)
  | .XOR rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.XOR)
  | .SRL rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SRL)
  | .SRA rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.SRA)
  | .OR rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.OR)
  | .AND rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPE rs2 rs1 rd rop.AND)
  | .FENCE rd rs1 fm pred succ => some (LeanRV64D.Functions.execute_FENCE fm pred succ rs1 rd)
  | .ECALL => some (LeanRV64D.Functions.execute_ECALL ())
  | .EBREAK => some (LeanRV64D.Functions.execute_EBREAK ())
  | .LWU rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd true 4)
  | .LD rd rs1 imm => some (LeanRV64D.Functions.execute_LOAD imm rs1 rd false 8)
  | .SD rs2 rs1 imm => some (LeanRV64D.Functions.execute_STORE imm rs2 rs1 8)
  | .ADDIW rd rs1 imm => some (LeanRV64D.Functions.execute_ADDIW imm rs1 rd)
  | .SLLIW rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW)
  | .SRLIW rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW)
  | .SRAIW rd rs1 shamt => some (LeanRV64D.Functions.execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW)
  | .ADDW rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPEW rs2 rs1 rd ropw.ADDW)
  | .SUBW rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPEW rs2 rs1 rd ropw.SUBW)
  | .SLLW rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPEW rs2 rs1 rd ropw.SLLW)
  | .SRLW rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPEW rs2 rs1 rd ropw.SRLW)
  | .SRAW rd rs1 rs2 => some (LeanRV64D.Functions.execute_RTYPEW rs2 rs1 rd ropw.SRAW)
  | .MUL rd rs1 rs2 => some (LeanRV64D.Functions.execute_MUL rs2 rs1 rd mulLow)
  | .MULH rd rs1 rs2 => some (LeanRV64D.Functions.execute_MUL rs2 rs1 rd mulHighSigned)
  | .MULHU rd rs1 rs2 => some (LeanRV64D.Functions.execute_MUL rs2 rs1 rd mulHighUnsigned)
  | .MULHSU rd rs1 rs2 => some (LeanRV64D.Functions.execute_MUL rs2 rs1 rd mulHighSignedUnsigned)
  | .DIV rd rs1 rs2 _quotient _remAbs => some (LeanRV64D.Functions.execute_DIV rs2 rs1 rd false)
  | .DIVU rd rs1 rs2 _quotient => some (LeanRV64D.Functions.execute_DIV rs2 rs1 rd true)
  | .REM rd rs1 rs2 _quotient _remAbs => some (LeanRV64D.Functions.execute_REM rs2 rs1 rd false)
  | .REMU rd rs1 rs2 _quotient => some (LeanRV64D.Functions.execute_REM rs2 rs1 rd true)
  | .MULW rd rs1 rs2 => some (LeanRV64D.Functions.execute_MULW rs2 rs1 rd)
  | .DIVW rd rs1 rs2 _quotient _remAbs => some (LeanRV64D.Functions.execute_DIVW rs2 rs1 rd false)
  | .DIVUW rd rs1 rs2 _quotient => some (LeanRV64D.Functions.execute_DIVW rs2 rs1 rd true)
  | .REMW rd rs1 rs2 _quotient _remAbs => some (LeanRV64D.Functions.execute_REMW rs2 rs1 rd false)
  | .REMUW rd rs1 rs2 _quotient => some (LeanRV64D.Functions.execute_REMW rs2 rs1 rd true)
  | .LR_W rd rs1 aq rl => some (LeanRV64D.Functions.execute_LOADRES aq rl rs1 4 rd)
  | .SC_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_STORECON aq rl rs2 rs1 4 rd)
  | .AMOSWAP_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOSWAP aq rl rs2 rs1 4 rd)
  | .AMOADD_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOADD aq rl rs2 rs1 4 rd)
  | .AMOXOR_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOXOR aq rl rs2 rs1 4 rd)
  | .AMOAND_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOAND aq rl rs2 rs1 4 rd)
  | .AMOOR_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOOR aq rl rs2 rs1 4 rd)
  | .AMOMIN_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMIN aq rl rs2 rs1 4 rd)
  | .AMOMAX_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMAX aq rl rs2 rs1 4 rd)
  | .AMOMINU_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMINU aq rl rs2 rs1 4 rd)
  | .AMOMAXU_W rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMAXU aq rl rs2 rs1 4 rd)
  | .LR_D rd rs1 aq rl => some (LeanRV64D.Functions.execute_LOADRES aq rl rs1 8 rd)
  | .SC_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_STORECON aq rl rs2 rs1 8 rd)
  | .AMOSWAP_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOSWAP aq rl rs2 rs1 8 rd)
  | .AMOADD_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOADD aq rl rs2 rs1 8 rd)
  | .AMOXOR_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOXOR aq rl rs2 rs1 8 rd)
  | .AMOAND_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOAND aq rl rs2 rs1 8 rd)
  | .AMOOR_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOOR aq rl rs2 rs1 8 rd)
  | .AMOMIN_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMIN aq rl rs2 rs1 8 rd)
  | .AMOMAX_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMAX aq rl rs2 rs1 8 rd)
  | .AMOMINU_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMINU aq rl rs2 rs1 8 rd)
  | .AMOMAXU_D rd rs1 rs2 aq rl => some (LeanRV64D.Functions.execute_AMO amoop.AMOMAXU aq rl rs2 rs1 8 rd)
  | .CSRRW rd csr rs1 => some (LeanRV64D.Functions.execute_CSRReg csr rs1 rd csrop.CSRRW)
  | .CSRRS rd csr rs1 => some (LeanRV64D.Functions.execute_CSRReg csr rs1 rd csrop.CSRRS)
  | .MRET => some (LeanRV64D.Functions.execute_MRET ())

private def expandedProgram? : Option JoltISA.Program → Option JoltISA.JoltExecution
  | some program => some (.expandedInstr program)
  | none => none

/-- Jolt-side execution for the guest source instruction.

`none` marks instructions that are in the Rust source profile but whose Jolt
program is intentionally left unwired here for now. -/
def joltExecution : RiscvInstruction → Option JoltISA.JoltExecution
  | .LUI rd imm =>
      some (.nativeInstr (.LUI (.xreg rd) (imm.setWidth 64)))
  | .AUIPC rd imm =>
      some (.nativeInstr (.AUIPC (.xreg rd) imm))
  | .JAL rd imm =>
      some (.nativeInstr (.JAL (.xreg rd) imm))
  | .JALR rd rs1 imm =>
      some (.nativeInstr (.JALR (.xreg rd) (.xreg rs1) imm))
  | .BEQ rs1 rs2 imm =>
      some (.nativeInstr (.BEQ (.xreg rs1) (.xreg rs2) imm))
  | .BNE rs1 rs2 imm =>
      some (.nativeInstr (.BNE (.xreg rs1) (.xreg rs2) imm))
  | .BLT rs1 rs2 imm =>
      some (.nativeInstr (.BLT (.xreg rs1) (.xreg rs2) imm))
  | .BGE rs1 rs2 imm =>
      some (.nativeInstr (.BGE (.xreg rs1) (.xreg rs2) imm))
  | .BLTU rs1 rs2 imm =>
      some (.nativeInstr (.BLTU (.xreg rs1) (.xreg rs2) imm))
  | .BGEU rs1 rs2 imm =>
      some (.nativeInstr (.BGEU (.xreg rs1) (.xreg rs2) imm))
  | .LB rd rs1 imm =>
      some (.expandedInstr (JoltISA.lbProgram imm rs1 rd))
  | .LH rd rs1 imm =>
      some (.expandedInstr (JoltISA.lhProgram imm rs1 rd))
  | .LW rd rs1 imm =>
      some (.expandedInstr (JoltISA.lwProgram imm rs1 rd))
  | .LBU rd rs1 imm =>
      some (.expandedInstr (JoltISA.lbuProgram imm rs1 rd))
  | .LHU rd rs1 imm =>
      some (.expandedInstr (JoltISA.lhuProgram imm rs1 rd))
  | .SB rs2 rs1 imm =>
      some (.expandedInstr (JoltISA.sbProgram imm rs2 rs1))
  | .SH rs2 rs1 imm =>
      some (.expandedInstr (JoltISA.shProgram imm rs2 rs1))
  | .SW rs2 rs1 imm =>
      some (.expandedInstr (JoltISA.swProgram imm rs2 rs1))
  | .ADDI rd rs1 imm =>
      some (.nativeInstr (.ADDI (.xreg rd) (.xreg rs1) imm))
  | .SLTI rd rs1 imm =>
      some (.nativeInstr (.SLTI (.xreg rd) (.xreg rs1) imm))
  | .SLTIU rd rs1 imm =>
      some (.nativeInstr (.SLTIU (.xreg rd) (.xreg rs1) imm))
  | .XORI rd rs1 imm =>
      some (.nativeInstr (.XORI (.xreg rd) (.xreg rs1) imm))
  | .ORI rd rs1 imm =>
      some (.nativeInstr (.ORI (.xreg rd) (.xreg rs1) imm))
  | .ANDI rd rs1 imm =>
      some (.nativeInstr (.ANDI (.xreg rd) (.xreg rs1) imm))
  | .SLLI rd rs1 shamt =>
      some (.expandedInstr (JoltISA.slliProgram shamt rs1 rd))
  | .SRLI rd rs1 shamt =>
      some (.expandedInstr (JoltISA.srliProgram shamt rs1 rd))
  | .SRAI rd rs1 shamt =>
      some (.expandedInstr (JoltISA.sraiProgram shamt rs1 rd))
  | .ADD rd rs1 rs2 =>
      some (.nativeInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SUB rd rs1 rs2 =>
      some (.nativeInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SLL rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.sllProgram rs2 rs1 rd))
  | .SLT rd rs1 rs2 =>
      some (.nativeInstr (.SLT (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SLTU rd rs1 rs2 =>
      some (.nativeInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .XOR rd rs1 rs2 =>
      some (.nativeInstr (.XOR (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SRL rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.srlProgram rs2 rs1 rd))
  | .SRA rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.sraProgram rs2 rs1 rd))
  | .OR rd rs1 rs2 =>
      some (.nativeInstr (.OR (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .AND rd rs1 rs2 =>
      some (.nativeInstr (.AND (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .FENCE _rd _rs1 _fm _pred _succ =>
      some (.nativeInstr .FENCE)
  | .ECALL =>
      some (.expandedInstr JoltISA.ecallProgram)
  | .EBREAK =>
      some (.expandedInstr JoltISA.ebreakProgram)
  | .LWU rd rs1 imm =>
      some (.expandedInstr (JoltISA.lwuProgram imm rs1 rd))
  | .LD rd rs1 imm =>
      some (.nativeInstr (.LD (.xreg rd) (.xreg rs1) imm))
  | .SD rs2 rs1 imm =>
      some (.nativeInstr (.SD (.xreg rs1) (.xreg rs2) imm))
  | .ADDIW rd rs1 imm =>
      some (.expandedInstr (JoltISA.addiwProgram imm rs1 rd))
  | .SLLIW rd rs1 shamt =>
      some (.expandedInstr (JoltISA.slliwProgram shamt rs1 rd))
  | .SRLIW rd rs1 shamt =>
      some (.expandedInstr (JoltISA.srliwProgram shamt rs1 rd))
  | .SRAIW rd rs1 shamt =>
      some (.expandedInstr (JoltISA.sraiwProgram shamt rs1 rd))
  | .ADDW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.addwProgram rs2 rs1 rd))
  | .SUBW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.subwProgram rs2 rs1 rd))
  | .SLLW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.sllwProgram rs2 rs1 rd))
  | .SRLW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.srlwProgram rs2 rs1 rd))
  | .SRAW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.srawProgram rs2 rs1 rd))
  | .MUL rd rs1 rs2 =>
      some (.nativeInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .MULH rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.mulhProgram rs2 rs1 rd))
  | .MULHU rd rs1 rs2 =>
      some (.nativeInstr (.MULHU (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .MULHSU rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.mulhsuProgram rs2 rs1 rd))
  | .DIV rd rs1 rs2 quotient remAbs =>
      some (.expandedInstr (JoltISA.divProgram rs2 rs1 rd quotient remAbs))
  | .DIVU rd rs1 rs2 quotient =>
      some (.expandedInstr (JoltISA.divuProgram rs2 rs1 rd quotient))
  | .REM rd rs1 rs2 quotient remAbs =>
      some (.expandedInstr (JoltISA.remProgram rs2 rs1 rd quotient remAbs))
  | .REMU rd rs1 rs2 quotient =>
      some (.expandedInstr (JoltISA.remuProgram rs2 rs1 rd quotient))
  | .MULW rd rs1 rs2 =>
      some (.expandedInstr (JoltISA.mulwProgram rs2 rs1 rd))
  | .DIVW rd rs1 rs2 quotient remAbs =>
      some (.expandedInstr (JoltISA.divwProgram rs2 rs1 rd quotient remAbs))
  | .DIVUW rd rs1 rs2 quotient =>
      some (.expandedInstr (JoltISA.divuwProgram rs2 rs1 rd quotient))
  | .REMW rd rs1 rs2 quotient remAbs =>
      some (.expandedInstr (JoltISA.remwProgram rs2 rs1 rd quotient remAbs))
  | .REMUW rd rs1 rs2 quotient =>
      some (.expandedInstr (JoltISA.remuwProgram rs2 rs1 rd quotient))
  | .LR_W _rd _rs1 _aq _rl => none
  | .SC_W _rd _rs1 _rs2 _aq _rl => none
  | .AMOSWAP_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoswapwProgram rs2 rs1 rd))
  | .AMOADD_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoaddwProgram rs2 rs1 rd))
  | .AMOXOR_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoxorwProgram rs2 rs1 rd))
  | .AMOAND_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoandwProgram rs2 rs1 rd))
  | .AMOOR_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoorwProgram rs2 rs1 rd))
  | .AMOMIN_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amominwProgram rs2 rs1 rd))
  | .AMOMAX_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amomaxwProgram rs2 rs1 rd))
  | .AMOMINU_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amominuwProgram rs2 rs1 rd))
  | .AMOMAXU_W rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amomaxuwProgram rs2 rs1 rd))
  | .LR_D _rd _rs1 _aq _rl => none
  | .SC_D _rd _rs1 _rs2 _aq _rl => none
  | .AMOSWAP_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoswapdProgram rs2 rs1 rd))
  | .AMOADD_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoadddProgram rs2 rs1 rd))
  | .AMOXOR_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoxordProgram rs2 rs1 rd))
  | .AMOAND_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoanddProgram rs2 rs1 rd))
  | .AMOOR_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amoordProgram rs2 rs1 rd))
  | .AMOMIN_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amomindProgram rs2 rs1 rd))
  | .AMOMAX_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amomaxdProgram rs2 rs1 rd))
  | .AMOMINU_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amominudProgram rs2 rs1 rd))
  | .AMOMAXU_D rd rs1 rs2 _aq _rl =>
      some (.expandedInstr (JoltISA.amomaxudProgram rs2 rs1 rd))
  | .CSRRW rd csr rs1 =>
      expandedProgram? (JoltISA.csrrwProgram? csr rs1 rd)
  | .CSRRS rd csr rs1 =>
      expandedProgram? (JoltISA.csrrsProgram? csr rs1 rd)
  | .MRET =>
      some (.expandedInstr JoltISA.mretProgram)

/-- Assumption payload for the equivalence statement.

The advice-backed ALU instructions all need source-register read facts; their
advice operands live in the `RiscvInstruction` constructor itself. -/
def equivAssumptions : (instr : RiscvInstruction) → SailJoltState → Type
  | .ADDW _rd rs1 rs2, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .DIV _rd rs1 rs2 _quotient _remAbs, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .DIVU _rd rs1 rs2 _quotient, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .REM _rd rs1 rs2 _quotient _remAbs, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .REMU _rd rs1 rs2 _quotient, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .DIVW _rd rs1 rs2 _quotient _remAbs, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .DIVUW _rd rs1 rs2 _quotient, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .REMW _rd rs1 rs2 _quotient _remAbs, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | .REMUW _rd rs1 rs2 _quotient, js =>
      ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  | _, _ => Unit

/-- Equivalence proposition selected by the operand-bearing instruction.

The fallback is deliberately `False` so unwired opcodes are visible gaps, not
vacuous successes. -/
def equivalenceStatement :
    (instr : RiscvInstruction) →
    (js : SailJoltState) →
    equivAssumptions instr js →
    Prop
  | instr, js, _h =>
    match instr with
    | .ADDW rd rs1 rs2 =>
      addwProgramEqSailStatement rs2 rs1 rd js _h
    | .DIV rd rs1 rs2 quotient remAbs =>
      divProgramEqSailStatement rs2 rs1 rd quotient remAbs js _h
    | .DIVU rd rs1 rs2 quotient =>
      divuProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .REM rd rs1 rs2 quotient remAbs =>
      remProgramEqSailStatement rs2 rs1 rd quotient remAbs js _h
    | .REMU rd rs1 rs2 quotient =>
      remuProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .DIVW rd rs1 rs2 quotient remAbs =>
      divwProgramEqSailStatement rs2 rs1 rd quotient remAbs js _h
    | .DIVUW rd rs1 rs2 quotient =>
      divuwProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .REMW rd rs1 rs2 quotient remAbs =>
      remwProgramEqSailStatement rs2 rs1 rd quotient remAbs js _h
    | .REMUW rd rs1 rs2 quotient =>
      remuwProgramEqSailStatement rs2 rs1 rd quotient js _h
    | _ => False

/-- Proof selector for the equivalence statement.

The fallback marks the remaining instruction branches that still need to be
connected to their existing instruction-equivalence theorems. -/
theorem equivalenceStatement_holds :
    (instr : RiscvInstruction) →
    (js : SailJoltState) →
    (h : equivAssumptions instr js) →
    equivalenceStatement instr js h
  | .ADDW rd rs1 rs2, js, h =>
      addwProgram_eq_sail rs2 rs1 rd js h
  | .DIV rd rs1 rs2 quotient remAbs, js, h =>
      divProgram_eq_sail rs2 rs1 rd quotient remAbs js h
  | .DIVU rd rs1 rs2 quotient, js, h =>
      divuProgram_eq_sail rs2 rs1 rd quotient js h
  | .REM rd rs1 rs2 quotient remAbs, js, h =>
      remProgram_eq_sail rs2 rs1 rd quotient remAbs js h
  | .REMU rd rs1 rs2 quotient, js, h =>
      remuProgram_eq_sail rs2 rs1 rd quotient js h
  | .DIVW rd rs1 rs2 quotient remAbs, js, h =>
      divwProgram_eq_sail rs2 rs1 rd quotient remAbs js h
  | .DIVUW rd rs1 rs2 quotient, js, h =>
      divuwProgram_eq_sail rs2 rs1 rd quotient js h
  | .REMW rd rs1 rs2 quotient remAbs, js, h =>
      remwProgram_eq_sail rs2 rs1 rd quotient remAbs js h
  | .REMUW rd rs1 rs2 quotient, js, h =>
      remuwProgram_eq_sail rs2 rs1 rd quotient js h
  | _, _, _ => by
      sorry

end RiscvInstruction
