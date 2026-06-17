import JoltBytecode.JoltISA.Instruction
import JoltBytecode.InstructionEquivalence.ProofSupport
/-!
# Guest RV64IMAC Opcode Universe

Guest compiler target evidence:
`riscv64imac-unknown-none-elf`

This says the guest program target ISA is RV64IMAC: RV64I base integer
instructions plus the M, A, and C extensions.

Official ISA references, RISC-V Ratified Specifications Library:
* RV64I base:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html
* M extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html
* A extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html
* C extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html

This file only records the guest-side opcode universe.  It deliberately does
not include Zicsr, privileged instructions, Jolt virtual/custom/advice
instructions, or proof/coverage metadata.
-/


/-- Architectural instruction mnemonics that may appear in an
`riscv64imac-unknown-none-elf` guest program. -/
inductive GuestRV64IMACOpcode where
  -- RV64I base integer instructions.
  | LUI
  | AUIPC
  | JAL
  | JALR
  | BEQ
  | BNE
  | BLT
  | BGE
  | BLTU
  | BGEU
  | LB
  | LH
  | LW
  | LBU
  | LHU
  | SB
  | SH
  | SW
  | ADDI
  | SLTI
  | SLTIU
  | XORI
  | ORI
  | ANDI
  | SLLI
  | SRLI
  | SRAI
  | ADD
  | SUB
  | SLL
  | SLT
  | SLTU
  | XOR
  | SRL
  | SRA
  | OR
  | AND
  | FENCE
  | ECALL
  | EBREAK
  | LWU
  | LD
  | SD
  | ADDIW
  | SLLIW
  | SRLIW
  | SRAIW
  | ADDW
  | SUBW
  | SLLW
  | SRLW
  | SRAW

  -- M extension.
  | MUL
  | MULH
  | MULHSU
  | MULHU
  | DIV
  | DIVU
  | REM
  | REMU
  | MULW
  | DIVW
  | DIVUW
  | REMW
  | REMUW

  -- A extension.
  | LR_W
  | SC_W
  | AMOSWAP_W
  | AMOADD_W
  | AMOXOR_W
  | AMOAND_W
  | AMOOR_W
  | AMOMIN_W
  | AMOMAX_W
  | AMOMINU_W
  | AMOMAXU_W
  | LR_D
  | SC_D
  | AMOSWAP_D
  | AMOADD_D
  | AMOXOR_D
  | AMOAND_D
  | AMOOR_D
  | AMOMIN_D
  | AMOMAX_D
  | AMOMINU_D
  | AMOMAXU_D

  -- C extension, restricted to RV64IMAC integer compressed instructions.
  | C_ADDI4SPN
  | C_LW
  | C_LD
  | C_SW
  | C_SD
  | C_NOP
  | C_ADDI
  | C_ADDIW
  | C_LI
  | C_ADDI16SP
  | C_LUI
  | C_SRLI
  | C_SRAI
  | C_ANDI
  | C_SUB
  | C_XOR
  | C_OR
  | C_AND
  | C_SUBW
  | C_ADDW
  | C_J
  | C_BEQZ
  | C_BNEZ
  | C_SLLI
  | C_LWSP
  | C_LDSP
  | C_JR
  | C_MV
  | C_EBREAK
  | C_JALR
  | C_ADD
  | C_SWSP
  | C_SDSP
  deriving Repr, DecidableEq

/-!
# Guest Opcode Interpretation Scaffold

`Completness.lean` owns only the guest RV64IMAC opcode universe.
This file is for connecting those opcodes to the Jolt side, Sail side, and
existing equivalence theorems.
-/

namespace JoltISA

/-- No-operand native Jolt targets used when interpreting guest RISC-V opcodes. -/
inductive NativeInstr where
  | Lui
  | Auipc
  | Jal
  | Jalr
  | Beq
  | Bne
  | Blt
  | Bge
  | BltU
  | BgeU
  | Addi
  | SltI
  | SltIU
  | XorI
  | OrI
  | AndI
  | Add
  | Sub
  | Slt
  | SltU
  | Xor
  | Or
  | And
  | Fence
  | Ld
  | Sd
  | Mul
  | MulHU
  deriving Repr, DecidableEq

/-- A guest RISC-V opcode is either native in the final Jolt ISA or expanded
before final Jolt bytecode. -/
inductive Implementation where
  | native (kind : NativeInstr)
  | expanded (kind : Expanded)
  deriving Repr, DecidableEq

namespace Completeness

/-- In Jolt, compressed guest instructions are uncompressed before Jolt handling. -/
def uncompressedInstruction : GuestRV64IMACOpcode → JoltISA.Implementation
  | .LUI => .native .Lui
  | .AUIPC => .native .Auipc
  | .JAL => .native .Jal
  | .JALR => .native .Jalr
  | .BEQ => .native .Beq
  | .BNE => .native .Bne
  | .BLT => .native .Blt
  | .BGE => .native .Bge
  | .BLTU => .native .BltU
  | .BGEU => .native .BgeU
  | .LB => .expanded .LB
  | .LH => .expanded .LH
  | .LW => .expanded .LW
  | .LBU => .expanded .LBU
  | .LHU => .expanded .LHU
  | .SB => .expanded .SB
  | .SH => .expanded .SH
  | .SW => .expanded .SW
  | .ADDI => .native .Addi
  | .SLTI => .native .SltI
  | .SLTIU => .native .SltIU
  | .XORI => .native .XorI
  | .ORI => .native .OrI
  | .ANDI => .native .AndI
  | .SLLI => .expanded .SLLI
  | .SRLI => .expanded .SRLI
  | .SRAI => .expanded .SRAI
  | .ADD => .native .Add
  | .SUB => .native .Sub
  | .SLL => .expanded .SLL
  | .SLT => .native .Slt
  | .SLTU => .native .SltU
  | .XOR => .native .Xor
  | .SRL => .expanded .SRL
  | .SRA => .expanded .SRA
  | .OR => .native .Or
  | .AND => .native .And
  | .FENCE => .native .Fence
  | .ECALL => .expanded .ECALL
  | .EBREAK => .expanded .EBREAK
  | .LWU => .expanded .LWU
  | .LD => .native .Ld
  | .SD => .native .Sd
  | .ADDIW => .expanded .ADDIW
  | .SLLIW => .expanded .SLLIW
  | .SRLIW => .expanded .SRLIW
  | .SRAIW => .expanded .SRAIW
  | .ADDW => .expanded .ADDW
  | .SUBW => .expanded .SUBW
  | .SLLW => .expanded .SLLW
  | .SRLW => .expanded .SRLW
  | .SRAW => .expanded .SRAW
  | .MUL => .native .Mul
  | .MULH => .expanded .MULH
  | .MULHSU => .expanded .MULHSU
  | .MULHU => .native .MulHU
  | .DIV => .expanded .DIV
  | .DIVU => .expanded .DIVU
  | .REM => .expanded .REM
  | .REMU => .expanded .REMU
  | .MULW => .expanded .MULW
  | .DIVW => .expanded .DIVW
  | .DIVUW => .expanded .DIVUW
  | .REMW => .expanded .REMW
  | .REMUW => .expanded .REMUW
  | .LR_W => .expanded .LRW
  | .SC_W => .expanded .SCW
  | .AMOSWAP_W => .expanded .AMOSWAPW
  | .AMOADD_W => .expanded .AMOADDW
  | .AMOXOR_W => .expanded .AMOXORW
  | .AMOAND_W => .expanded .AMOANDW
  | .AMOOR_W => .expanded .AMOORW
  | .AMOMIN_W => .expanded .AMOMINW
  | .AMOMAX_W => .expanded .AMOMAXW
  | .AMOMINU_W => .expanded .AMOMINUW
  | .AMOMAXU_W => .expanded .AMOMAXUW
  | .LR_D => .expanded .LRD
  | .SC_D => .expanded .SCD
  | .AMOSWAP_D => .expanded .AMOSWAPD
  | .AMOADD_D => .expanded .AMOADDD
  | .AMOXOR_D => .expanded .AMOXORD
  | .AMOAND_D => .expanded .AMOANDD
  | .AMOOR_D => .expanded .AMOORD
  | .AMOMIN_D => .expanded .AMOMIND
  | .AMOMAX_D => .expanded .AMOMAXD
  | .AMOMINU_D => .expanded .AMOMINUD
  | .AMOMAXU_D => .expanded .AMOMAXUD
  | .C_ADDI4SPN => .native .Addi
  | .C_LW => .expanded .LW
  | .C_LD => .native .Ld
  | .C_SW => .expanded .SW
  | .C_SD => .native .Sd
  | .C_NOP => .native .Addi
  | .C_ADDI => .native .Addi
  | .C_ADDIW => .expanded .ADDIW
  | .C_LI => .native .Addi
  | .C_ADDI16SP => .native .Addi
  | .C_LUI => .native .Lui
  | .C_SRLI => .expanded .SRLI
  | .C_SRAI => .expanded .SRAI
  | .C_ANDI => .native .AndI
  | .C_SUB => .native .Sub
  | .C_XOR => .native .Xor
  | .C_OR => .native .Or
  | .C_AND => .native .And
  | .C_SUBW => .expanded .SUBW
  | .C_ADDW => .expanded .ADDW
  | .C_J => .native .Jal
  | .C_BEQZ => .native .Beq
  | .C_BNEZ => .native .Bne
  | .C_SLLI => .expanded .SLLI
  | .C_LWSP => .expanded .LW
  | .C_LDSP => .native .Ld
  | .C_JR => .native .Jalr
  | .C_MV => .native .Add
  | .C_EBREAK => .expanded .EBREAK
  | .C_JALR => .native .Jalr
  | .C_ADD => .native .Add
  | .C_SWSP => .expanded .SW
  | .C_SDSP => .native .Sd

/-- Minimal per-opcode interpretation entry. -/
structure RiscvInstruction (op : GuestRV64IMACOpcode) where
  implementation : JoltISA.Implementation

def instructionOf : (op : GuestRV64IMACOpcode) → RiscvInstruction op
  | .ADDW => { implementation := .expanded .ADDW }
  | .SRL => { implementation := .expanded .SRL }
  | .ADD => { implementation := .native .Add }
  | .C_ADDW => { implementation := .expanded .ADDW }
  | .C_ADD => { implementation := .native .Add }
  | op => { implementation := uncompressedInstruction op }

end Completeness
end JoltISA
