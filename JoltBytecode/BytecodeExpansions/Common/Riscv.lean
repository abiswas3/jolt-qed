import Mathlib.Tactic
import Mathlib.Data.BitVec
import JoltBytecode.BytecodeExpansions.Common.Cpu

variable {w : Nat}

namespace Riscv

-- ============================================================================
-- Base Integer Instructions (generic over width)
-- ============================================================================

/-- SUB rd, rs1, rs2: subtraction. rd = rs1 - rs2 -/
def sub (x y : BitVec w) : BitVec w :=
  x - y

/-- ADD rd, rs1, rs2: addition. rd = rs1 + rs2 -/
def add (x y : BitVec w) : BitVec w :=
  x + y

/-- SUBW rd, rs1, rs2 (RV64I): subtract lower 32 bits and sign-extend to 64 bits.
    rd = signExtend(rs1[31:0] - rs2[31:0]) -/
def subw (x y : BitVec 64) : BitVec 64 :=
  (x.setWidth 32 - y.setWidth 32).signExtend 64

/-- SRLIW rd, rs1, shamt (RV64I): logical right shift of lower 32 bits by shamt,
    sign-extend the 32-bit result to 64 bits.
    rd = signExtend(rs1[31:0] >>> shamt) -/
def srliw (x : BitVec 64) (shamt : BitVec 64) : BitVec 64 :=
  ((x.setWidth 32) >>> shamt.toNat).signExtend 64

-- ============================================================================
-- Multiply Extension (generic over width)
-- ============================================================================

/-- MUL rd, rs1, rs2: multiplication (lower w bits of product). -/
def mul (x y : BitVec w) : BitVec w :=
  x * y

/-- MULHU rd, rs1, rs2: unsigned high multiplication.
    Returns upper w bits of the unsigned 2w-bit product. -/
def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

/-- MULH rd, rs1, rs2: signed high multiplication.
    Returns upper w bits of the signed 2w-bit product. -/
def mulh (x y : BitVec w) : BitVec w :=
  BitVec.ofInt w (x.toInt * y.toInt / (2 ^ w : Int))

end Riscv

-- ============================================================================
-- Load/Store helpers and instructions (require State)
-- ============================================================================

-- Nat value of 4 little-endian bytes at addr.
def read_word_val (addr : BitVec 64) (s : State) : Nat :=
  (read_mem addr s).toNat +
  (read_mem (addr + 1) s).toNat * 2^8 +
  (read_mem (addr + 2) s).toNat * 2^16 +
  (read_mem (addr + 3) s).toNat * 2^24

-- BitVec wrapper: read a 32-bit word from memory.
def read_word (addr : BitVec 64) (s : State) : BitVec 32 :=
  BitVec.ofNat 32 (read_word_val addr s)

namespace Riscv

/-- LW rd, offset(rs1) (RV32I/RV64I): load a 32-bit word from memory at the
    word-aligned address (rs1 + sign_extend(offset)) & ~3, sign-extend to 64 bits.
    rd = signExtend(mem[addr..addr+3]) -/
def lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base := read rs1 s.reg
  let addr := (imm.setWidth 64 + base) &&& (-4#64)
  let word := read_word addr s
  let new_reg := write rd (word.signExtend 64) s.reg
  { s with reg := new_reg }

end Riscv
