import Mathlib.Tactic
import Mathlib.Data.BitVec

/-- VirtualSignExtend: Sign-extend (only valid for 64 bit)
    This is the BitVec-valued counterpart of `signExtract`. -/
def virtualMovSign (x : BitVec w) : BitVec w :=
  BitVec.ofInt w (signExtract x)



