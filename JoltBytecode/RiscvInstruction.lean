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
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoaddd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoaddw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoandd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoandw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxud
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxuw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomind
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominud
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominuw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoord
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoorw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoswapd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoswapw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoxord
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoxorw

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
  | .AMOSWAP_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js
  | .AMOADD_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js
  | .AMOXOR_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js
  | .AMOAND_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOAND rs2 rs1 rd js
  | .AMOOR_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js
  | .AMOMIN_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js
  | .AMOMAX_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js
  | .AMOMINU_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js
  | .AMOMAXU_W rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoWordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js
  | .AMOSWAP_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js
  | .AMOADD_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js
  | .AMOXOR_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js
  | .AMOAND_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOAND rs2 rs1 rd js
  | .AMOOR_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js
  | .AMOMIN_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js
  | .AMOMAX_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js
  | .AMOMINU_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js
  | .AMOMAXU_D rd rs1 rs2 _aq _rl, js =>
      AtomicFamily.AmoDwordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js
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
    | .AMOSWAP_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoswapwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOADD_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoaddwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOXOR_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoxorwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOAND_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoandwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOOR_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoorwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMIN_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAX_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMINU_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominuwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAXU_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxuwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOSWAP_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoswapdProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOADD_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoadddProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOXOR_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoxordProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOAND_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoanddProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOOR_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoordProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMIN_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomindProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAX_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxdProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMINU_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominudProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAXU_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxudProgramEqSailStatement rs2 rs1 rd js _h
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
  | .AMOSWAP_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoswapwProgram_eq_sail rs2 rs1 rd js h
  | .AMOADD_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoaddwProgram_eq_sail rs2 rs1 rd js h
  | .AMOXOR_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoxorwProgram_eq_sail rs2 rs1 rd js h
  | .AMOAND_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoandwProgram_eq_sail rs2 rs1 rd js h
  | .AMOOR_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoorwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMIN_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAX_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMINU_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominuwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAXU_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxuwProgram_eq_sail rs2 rs1 rd js h
  | .AMOSWAP_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoswapdProgram_eq_sail rs2 rs1 rd js h
  | .AMOADD_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoadddProgram_eq_sail rs2 rs1 rd js h
  | .AMOXOR_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoxordProgram_eq_sail rs2 rs1 rd js h
  | .AMOAND_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoanddProgram_eq_sail rs2 rs1 rd js h
  | .AMOOR_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoordProgram_eq_sail rs2 rs1 rd js h
  | .AMOMIN_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomindProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAX_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxdProgram_eq_sail rs2 rs1 rd js h
  | .AMOMINU_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominudProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAXU_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxudProgram_eq_sail rs2 rs1 rd js h
  | _, _, _ => by
      sorry

end RiscvInstruction
