import JoltBytecode.InstructionEquivalence.AdviceFamily.VirtualAdvice

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Sail-side spec for `ADVICELH`: write the sign-extended advised halfword to `rd`. -/
def execute_ADVICELH (rd : regidx) (advice : BitVec 16) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

/-- Jolt inline for `ADVICELH`: advice load, then `SLLI 48`, then `SRAI 48`. -/
def jolt_advicelh (rd : regidx) (advice : BitVec 16) : JoltMonad ExecutionResult := do
  jolt_virtual_advice_load rd (advice.setWidth 64)
  let _ ← liftSail (execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SLLI)
  let _ ← liftSail (execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SRAI)
  pure RETIRE_SUCCESS

def execute_ADVICELH_inline (rd : regidx) (advice : BitVec 16) : SailM ExecutionResult := do
  wX_bits rd (advice.setWidth 64)
  let _ ← execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SLLI
  let _ ← execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SRAI
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_16 (advice : BitVec 16) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (48 : BitVec 6)) (48 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_16 advice

/-- Main theorem for `ADVICELH`: the inline Sail program collapses to the compact spec. -/
theorem execute_ADVICELH_inline_eq_spec (rd : regidx) (advice : BitVec 16)
    (hrd : rd ≠ regidx.Regidx 0) :
    execute_ADVICELH_inline rd advice = execute_ADVICELH rd advice := by
  simpa [execute_ADVICELH_inline, execute_ADVICELH] using
    execute_advice_inline_eq_spec_nonzero rd hrd (advice.setWidth 64)
      (sign_extend (m := 64) advice) (48 : BitVec 6)
      (advice_shift_sign_extend_16 advice)

theorem jolt_advicelh_eq_inline
    (rd : regidx) (advice : BitVec 16) (js : SailJoltState) :
    projectResult ((jolt_advicelh rd advice).run js) =
      (execute_ADVICELH_inline rd advice).run js.sail := by
  simpa [jolt_advicelh, jolt_virtual_advice_load, execute_ADVICELH_inline] using
    (projectResult_liftSail_seq3
      (wX_bits rd (advice.setWidth 64))
      (execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SLLI)
      (execute_SHIFTIOP (48 : BitVec 6) rd rd sop.SRAI)
      js)

end
