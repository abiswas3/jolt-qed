import Mathlib.Tactic
import Mathlib.Data.BitVec
import JoltBytecode.BytecodeExpansions.Common.Cpu

variable {w : Nat}

/-- Sign extraction: returns -1 if the bitvector is negative (msb set), 0 otherwise.
    This is the Int-valued version used in mathematical reasoning. -/
def signExtract (x : BitVec w) : Int :=
  if x.msb then -1 else 0

/-- Count trailing zeros of a natural number. Returns 0 for input 0. -/
-- Add a bit more documentation on this still of functin 
def ctz (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + ctz (n / 2)
termination_by n

-- Given natural number n -- The binary representation of 
-- This theorem proves that 2^n has exactly n trailing zeroes
@[simp] lemma ctz_pow2 (n : Nat) : ctz (2 ^ n) = n := by
  induction n with
  | zero => unfold ctz; simp
  | succ k ih =>
    unfold ctz
    rw [if_neg (show 2 ^ (k + 1) ≠ 0 from Nat.pos_iff_ne_zero.mp (by positivity))]
    rw [if_neg (show ¬(2 ^ (k + 1) % 2 = 1) from by rw [pow_succ]; omega)]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k from by rw [pow_succ]; omega]
    rw [ih]; omega

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

/-- VirtualSRLI: logical right shift by an immediate amount.
    The shift amount is the number of trailing zeros of the immediate operand,
    matching the Jolt/Rust implementation: `imm.trailing_zeros()`. -/
def virtualSRLI (x : BitVec w) (imm : Nat) : BitVec w :=
  x >>> ctz imm

/-- VirtualAssertWordAlignment: checks word alignment. If misaligned, sets the
    state error flag (like a panic). The returned address is unchanged; on error
    subsequent operations should not execute. -/
def virtualAssertWordAlignment (addr : BitVec 64) (s : State) : BitVec 64 × State :=
  if addr &&& 3#64 ≠ 0#64 then (addr, { s with error := true })
  else (addr, s)

/-- VirtualSignExtendWord: sign-extends the lower 32 bits of a 64-bit value.
    Interprets bits [31:0] as a signed 32-bit integer and produces the
    64-bit sign-extended result. -/
def virtualSignExtendWord (z : BitVec 64) : BitVec 64 :=
  (z.setWidth 32).signExtend 64

/-- VirtualPow2: compute 2^(x[5:0]) as a 64-bit value.
    Used by SLL to convert 6-bit shift amounts to multiplicands. -/
def virtualPow2 (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 6).toNat)

/-- VirtualPow2W: compute 2^(x[4:0]) as a 64-bit value.
    Used by SLLW to convert 5-bit shift amounts to multiplicands. -/
def virtualPow2W (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 5).toNat)

end Jolt
