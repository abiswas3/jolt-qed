import LeanRV64D.Defs

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

/-- Compressed primed registers denote the architectural register subset
`x8`-`x15`; the subset constraint is recorded later as a predicate. -/
abbrev CReg := regidx

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
  | SLLI (rd rs1 : regidx) (shamt : BitVec 5)
  | SRLI (rd rs1 : regidx) (shamt : BitVec 5)
  | SRAI (rd rs1 : regidx) (shamt : BitVec 5)
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
  | C_ADDI4SPN (rd' : CReg) (nzuimm : BitVec 10)
  | C_LW (rd' rs1' : CReg) (uimm : BitVec 7)
  | C_LD (rd' rs1' : CReg) (uimm : BitVec 8)
  | C_SW (rs2' rs1' : CReg) (uimm : BitVec 7)
  | C_SD (rs2' rs1' : CReg) (uimm : BitVec 8)
  | C_NOP
  | C_ADDI (rd : regidx) (nzimm : BitVec 6)
  | C_ADDIW (rd : regidx) (imm : BitVec 6)
  | C_LI (rd : regidx) (imm : BitVec 6)
  | C_ADDI16SP (nzimm : BitVec 10)
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
  | C_J (imm : BitVec 12)
  | C_BEQZ (rs1' : CReg) (imm : BitVec 9)
  | C_BNEZ (rs1' : CReg) (imm : BitVec 9)
  | C_SLLI (rd : regidx) (shamt : BitVec 6)
  | C_LWSP (rd : regidx) (uimm : BitVec 8)
  | C_LDSP (rd : regidx) (uimm : BitVec 9)
  | C_JR (rs1 : regidx)
  | C_MV (rd rs2 : regidx)
  | C_EBREAK
  | C_JALR (rs1 : regidx)
  | C_ADD (rd rs2 : regidx)
  | C_SWSP (rs2 : regidx) (uimm : BitVec 8)
  | C_SDSP (rs2 : regidx) (uimm : BitVec 9)

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
