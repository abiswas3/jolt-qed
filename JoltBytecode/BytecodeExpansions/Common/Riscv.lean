import Mathlib.Tactic
import Mathlib.Data.BitVec

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
