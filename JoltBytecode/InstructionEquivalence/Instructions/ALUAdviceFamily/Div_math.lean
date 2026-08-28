import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import Mathlib

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Architectural DIV/REM values

These definitions transcribe the pure values written by Sail. The old
arithmetic lemmas for the former two-advice signed expansion were removed when
Rust changed that expansion to its one-advice magnitude construction.
-/

/-- The pure 64-bit value written by execute_DIV. -/
def sail_div_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let quotient :=
    if (rs2_int == 0) then -1 else Int.tdiv rs1_int rs2_int
  let quotient :=
    if LeanRV64D.Functions.not is_unsigned &&
        (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))
    then -(2 ^i (LeanRV64D.Functions.xlen -i 1))
    else quotient
  to_bits_truncate (l := 64) quotient

/-- The pure 64-bit value written by execute_REM. -/
def sail_rem_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let remainder :=
    if (rs2_int == 0) then rs1_int else Int.tmod rs1_int rs2_int
  to_bits_truncate (l := 64) remainder

/-- Absolute value of a signed 64-bit bit-vector. -/
def bv_abs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

/-- The single advice word emitted by Rust for `REM`.

Rust uses zero advice on division by zero; otherwise it supplies the unsigned
magnitude of the signed quotient. -/
def rem_advice_value
    (dividend divisor : BitVec 64) : BitVec 64 :=
  if divisor = 0#64 then 0
  else bv_abs (sail_div_value dividend divisor false)

end
