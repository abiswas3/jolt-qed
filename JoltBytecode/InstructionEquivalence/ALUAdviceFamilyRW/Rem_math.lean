import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `jolt_rem`

REM uses the same signed division guards as DIV. The advice pair is still
`(quotient, |remainder|)`, but the architectural writeback is the signed
remainder reconstructed from `|remainder|` and the dividend sign.
-/

/-- Honest `|remainder|`, sign-corrected using the dividend sign, is exactly
Sail's signed REM result. -/
theorem signed_rem_of_honest_abs_eq_sail_rem (dividend divisor : BitVec 64) :
    ((bv_abs (sail_rem_value dividend divisor false) ^^^ dividend.sshiftRight 63) -
        dividend.sshiftRight 63) =
      sail_rem_value dividend divisor false := by
  by_cases hzero : divisor = 0#64
  · rw [sail_rem_value_of_zero dividend divisor hzero]
    exact x_eq_bv_abs_xor_sub_sign dividend
  · rw [sail_rem_value_of_normal dividend divisor hzero]
    exact srem_xor_sub_sign_eq_srem dividend divisor hzero

end
