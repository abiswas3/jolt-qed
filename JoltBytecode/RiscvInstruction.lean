import LeanRV64D.InstsEnd

/-!
# RISC-V Instructions

This file records an operand-bearing RISC-V instruction universe from the
official RISC-V ISA documentation only.

Rust/Jolt code is intentionally not cited here. Rust is the source of truth for
`JoltISA`; the RISC-V ISA docs are the source of truth for this file.
-/

open Sail PreSail

/-- A CSR address is the 12-bit `csr` field used by Zicsr instructions. -/
abbrev CsrAddr := BitVec 12

/-- The 5-bit unsigned immediate operand used by Zicsr immediate forms. -/
abbrev CsrUImm := BitVec 5

/-- `fm`, `pred`, and `succ` are 4-bit FENCE fields. -/
abbrev FenceField := BitVec 4

/-- Compressed primed registers denote the architectural register subset `x8`-`x15`. -/
abbrev CReg := cregidx

/-- Official RISC-V instruction constructors with operands.

Sources:
* RV32I base integer instructions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html
* RV64I base integer additions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html
* M extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html
* A extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html
* C extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html
* Zicsr extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html
* Privileged instruction listings:
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
  | DIV (rd rs1 rs2 : regidx)
  | DIVU (rd rs1 rs2 : regidx)
  | REM (rd rs1 rs2 : regidx)
  | REMU (rd rs1 rs2 : regidx)
  | MULW (rd rs1 rs2 : regidx)
  | DIVW (rd rs1 rs2 : regidx)
  | DIVUW (rd rs1 rs2 : regidx)
  | REMW (rd rs1 rs2 : regidx)
  | REMUW (rd rs1 rs2 : regidx)

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

  /- C extension for compressed instructions, RV64 integer subset.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html -/
  | C_ADDI4SPN (rd' : CReg) (nzuimm : BitVec 8)
  | C_LW (rd' rs1' : CReg) (uimm : BitVec 5)
  | C_LD (rd' rs1' : CReg) (uimm : BitVec 5)
  | C_SW (rs2' rs1' : CReg) (uimm : BitVec 5)
  | C_SD (rs2' rs1' : CReg) (uimm : BitVec 5)
  | C_NOP
  | C_ADDI (rd : regidx) (nzimm : BitVec 6)
  | C_ADDIW (rd : regidx) (imm : BitVec 6)
  | C_LI (rd : regidx) (imm : BitVec 6)
  | C_ADDI16SP (nzimm : BitVec 6)
  | C_LUI (rd : regidx) (nzimm : BitVec 6)
  | C_SRLI (rd' : CReg) (shamt : BitVec 6)
  | C_SRAI (rd' : CReg) (shamt : BitVec 6)
  | C_ANDI (rd' : CReg) (imm : BitVec 6)
  | C_SUB (rd' rs2' : CReg)
  | C_XOR (rd' rs2' : CReg)
  | C_OR (rd' rs2' : CReg)
  | C_AND (rd' rs2' : CReg)
  | C_SUBW (rd' rs2' : CReg)
  | C_ADDW (rd' rs2' : CReg)
  | C_J (imm : BitVec 11)
  | C_BEQZ (rs1' : CReg) (imm : BitVec 8)
  | C_BNEZ (rs1' : CReg) (imm : BitVec 8)
  | C_SLLI (rd : regidx) (shamt : BitVec 6)
  | C_LWSP (rd : regidx) (uimm : BitVec 6)
  | C_LDSP (rd : regidx) (uimm : BitVec 6)
  | C_JR (rs1 : regidx)
  | C_MV (rd rs2 : regidx)
  | C_EBREAK
  | C_JALR (rs1 : regidx)
  | C_ADD (rd rs2 : regidx)
  | C_SWSP (rs2 : regidx) (uimm : BitVec 6)
  | C_SDSP (rs2 : regidx) (uimm : BitVec 6)

  /- Zicsr extension for control and status register instructions.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html -/
  | CSRRW (rd : regidx) (csr : CsrAddr) (rs1 : regidx)
  | CSRRS (rd : regidx) (csr : CsrAddr) (rs1 : regidx)
  | CSRRC (rd : regidx) (csr : CsrAddr) (rs1 : regidx)
  | CSRRWI (rd : regidx) (csr : CsrAddr) (uimm : CsrUImm)
  | CSRRSI (rd : regidx) (csr : CsrAddr) (uimm : CsrUImm)
  | CSRRCI (rd : regidx) (csr : CsrAddr) (uimm : CsrUImm)

  /- Privileged instruction set listings.
     Source: https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html -/
  | SRET
  | MRET
  | MNRET
  | WFI
  | SCTRCLR
  | SFENCE_VMA (rs1 rs2 : regidx)
  | HFENCE_VVMA (rs1 rs2 : regidx)
  | HFENCE_GVMA (rs1 rs2 : regidx)
  | HLV_B (rd rs1 : regidx)
  | HLV_BU (rd rs1 : regidx)
  | HLV_H (rd rs1 : regidx)
  | HLV_HU (rd rs1 : regidx)
  | HLV_W (rd rs1 : regidx)
  | HLV_WU (rd rs1 : regidx)
  | HLV_D (rd rs1 : regidx)
  | HLVX_HU (rd rs1 : regidx)
  | HLVX_WU (rd rs1 : regidx)
  | HSV_B (rs2 rs1 : regidx)
  | HSV_H (rs2 rs1 : regidx)
  | HSV_W (rs2 rs1 : regidx)
  | HSV_D (rs2 rs1 : regidx)
  | SINVAL_VMA (rs1 rs2 : regidx)
  | SFENCE_W_INVAL
  | SFENCE_INVAL_IR
  | HINVAL_VVMA (rs1 rs2 : regidx)
  | HINVAL_GVMA (rs1 rs2 : regidx)
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
  | .DIV rd rs1 rs2 => some (LeanRV64D.Functions.execute_DIV rs2 rs1 rd false)
  | .DIVU rd rs1 rs2 => some (LeanRV64D.Functions.execute_DIV rs2 rs1 rd true)
  | .REM rd rs1 rs2 => some (LeanRV64D.Functions.execute_REM rs2 rs1 rd false)
  | .REMU rd rs1 rs2 => some (LeanRV64D.Functions.execute_REM rs2 rs1 rd true)
  | .MULW rd rs1 rs2 => some (LeanRV64D.Functions.execute_MULW rs2 rs1 rd)
  | .DIVW rd rs1 rs2 => some (LeanRV64D.Functions.execute_DIVW rs2 rs1 rd false)
  | .DIVUW rd rs1 rs2 => some (LeanRV64D.Functions.execute_DIVW rs2 rs1 rd true)
  | .REMW rd rs1 rs2 => some (LeanRV64D.Functions.execute_REMW rs2 rs1 rd false)
  | .REMUW rd rs1 rs2 => some (LeanRV64D.Functions.execute_REMW rs2 rs1 rd true)
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
  | .C_ADDI4SPN rd' nzuimm => some (pureResult (LeanRV64D.Functions.execute_C_ADDI4SPN rd' nzuimm))
  | .C_LW rd' rs1' uimm => some (pureResult (LeanRV64D.Functions.execute_C_LW uimm rs1' rd'))
  | .C_LD rd' rs1' uimm => some (pureResult (LeanRV64D.Functions.execute_C_LD uimm rs1' rd'))
  | .C_SW rs2' rs1' uimm => some (pureResult (LeanRV64D.Functions.execute_C_SW uimm rs1' rs2'))
  | .C_SD rs2' rs1' uimm => some (pureResult (LeanRV64D.Functions.execute_C_SD uimm rs1' rs2'))
  | .C_NOP => some (pureResult (LeanRV64D.Functions.execute_C_NOP 0b000000#6))
  | .C_ADDI rd nzimm => some (pureResult (LeanRV64D.Functions.execute_C_ADDI nzimm rd))
  | .C_ADDIW rd imm => some (pureResult (LeanRV64D.Functions.execute_C_ADDIW imm rd))
  | .C_LI rd imm => some (pureResult (LeanRV64D.Functions.execute_C_LI imm rd))
  | .C_ADDI16SP nzimm => some (pureResult (LeanRV64D.Functions.execute_C_ADDI16SP nzimm))
  | .C_LUI rd nzimm => some (pureResult (LeanRV64D.Functions.execute_C_LUI nzimm rd))
  | .C_SRLI rd' shamt => some (pureResult (LeanRV64D.Functions.execute_C_SRLI shamt rd'))
  | .C_SRAI rd' shamt => some (pureResult (LeanRV64D.Functions.execute_C_SRAI shamt rd'))
  | .C_ANDI rd' imm => some (pureResult (LeanRV64D.Functions.execute_C_ANDI imm rd'))
  | .C_SUB rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_SUB rd' rs2'))
  | .C_XOR rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_XOR rd' rs2'))
  | .C_OR rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_OR rd' rs2'))
  | .C_AND rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_AND rd' rs2'))
  | .C_SUBW rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_SUBW rd' rs2'))
  | .C_ADDW rd' rs2' => some (pureResult (LeanRV64D.Functions.execute_C_ADDW rd' rs2'))
  | .C_J imm => some (pureResult (LeanRV64D.Functions.execute_C_J imm))
  | .C_BEQZ rs1' imm => some (pureResult (LeanRV64D.Functions.execute_C_BEQZ imm rs1'))
  | .C_BNEZ rs1' imm => some (pureResult (LeanRV64D.Functions.execute_C_BNEZ imm rs1'))
  | .C_SLLI rd shamt => some (pureResult (LeanRV64D.Functions.execute_C_SLLI shamt rd))
  | .C_LWSP rd uimm => some (pureResult (LeanRV64D.Functions.execute_C_LWSP uimm rd))
  | .C_LDSP rd uimm => some (pureResult (LeanRV64D.Functions.execute_C_LDSP uimm rd))
  | .C_JR rs1 => some (pureResult (LeanRV64D.Functions.execute_C_JR rs1))
  | .C_MV rd rs2 => some (pureResult (LeanRV64D.Functions.execute_C_MV rd rs2))
  | .C_EBREAK => some (pureResult (LeanRV64D.Functions.execute_C_EBREAK ()))
  | .C_JALR rs1 => some (pureResult (LeanRV64D.Functions.execute_C_JALR rs1))
  | .C_ADD rd rs2 => some (pureResult (LeanRV64D.Functions.execute_C_ADD rd rs2))
  | .C_SWSP rs2 uimm => some (pureResult (LeanRV64D.Functions.execute_C_SWSP uimm rs2))
  | .C_SDSP rs2 uimm => some (pureResult (LeanRV64D.Functions.execute_C_SDSP uimm rs2))
  | .CSRRW rd csr rs1 => some (LeanRV64D.Functions.execute_CSRReg csr rs1 rd csrop.CSRRW)
  | .CSRRS rd csr rs1 => some (LeanRV64D.Functions.execute_CSRReg csr rs1 rd csrop.CSRRS)
  | .CSRRC rd csr rs1 => some (LeanRV64D.Functions.execute_CSRReg csr rs1 rd csrop.CSRRC)
  | .CSRRWI rd csr uimm => some (LeanRV64D.Functions.execute_CSRImm csr uimm rd csrop.CSRRW)
  | .CSRRSI rd csr uimm => some (LeanRV64D.Functions.execute_CSRImm csr uimm rd csrop.CSRRS)
  | .CSRRCI rd csr uimm => some (LeanRV64D.Functions.execute_CSRImm csr uimm rd csrop.CSRRC)
  | .SRET => some (LeanRV64D.Functions.execute_SRET ())
  | .MRET => some (LeanRV64D.Functions.execute_MRET ())
  | .MNRET => none
  | .WFI => some (LeanRV64D.Functions.execute_WFI ())
  | .SCTRCLR => none
  | .SFENCE_VMA rs1 rs2 => some (LeanRV64D.Functions.execute_SFENCE_VMA rs1 rs2)
  | .HFENCE_VVMA _ _ => none
  | .HFENCE_GVMA _ _ => none
  | .HLV_B _ _ => none
  | .HLV_BU _ _ => none
  | .HLV_H _ _ => none
  | .HLV_HU _ _ => none
  | .HLV_W _ _ => none
  | .HLV_WU _ _ => none
  | .HLV_D _ _ => none
  | .HLVX_HU _ _ => none
  | .HLVX_WU _ _ => none
  | .HSV_B _ _ => none
  | .HSV_H _ _ => none
  | .HSV_W _ _ => none
  | .HSV_D _ _ => none
  | .SINVAL_VMA rs1 rs2 => some (LeanRV64D.Functions.execute_SINVAL_VMA rs1 rs2)
  | .SFENCE_W_INVAL => some (LeanRV64D.Functions.execute_SFENCE_W_INVAL ())
  | .SFENCE_INVAL_IR => some (LeanRV64D.Functions.execute_SFENCE_INVAL_IR ())
  | .HINVAL_VVMA _ _ => none
  | .HINVAL_GVMA _ _ => none

end RiscvInstruction
