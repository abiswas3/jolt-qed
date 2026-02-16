import Mathlib.Tactic
import Mathlib.Data.BitVec

variable {w : Nat}

/-- Sign extraction: returns -1 if the bitvector is negative (msb set), 0 otherwise.
    This is the Int-valued version used in mathematical reasoning. -/
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0

-- Virtual instruction definitions for Jolt's bytecode expansion.
namespace Jolt

/-- VirtualMovSign: extracts the sign bit as a w-bit register value.
    Produces allOnes (two's complement -1) if negative, 0 otherwise.
    This is the BitVec-valued counterpart of `signExtract`. -/
def virtualMovSign (x : BitVec w) : BitVec w :=
  BitVec.ofInt w (signExtract x)

/-- MULHU: unsigned high multiplication.
    Computes the upper w bits of the unsigned product of x and y:
      floor(toNat(x) * toNat(y) / 2^w) -/
def mulhu (x y : BitVec w) : BitVec w :=
  BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)

/-- VirtualSignExtendWord: sign-extends the lower 32 bits of a 64-bit value.
    Interprets bits [31:0] as a signed 32-bit integer and produces the
    64-bit sign-extended result. -/
def virtualSignExtendWord (z : BitVec 64) : BitVec 64 :=
  (z.setWidth 32).signExtend 64

end Jolt
