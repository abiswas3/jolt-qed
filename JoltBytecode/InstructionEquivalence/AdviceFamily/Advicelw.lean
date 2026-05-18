import JoltBytecode.InstructionEquivalence.AdviceFamily.Advice

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Sail-side spec for `ADVICELW`: write the sign-extended advised word to `rd`. -/
def execute_ADVICELW (rd : regidx) (advice : BitVec 32) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

/-- Jolt inline for `ADVICELW`: advice load, then `SLLI 32`, then `SRAI 32`. -/
def jolt_advicelw (rd : regidx) (advice : BitVec 32) : JoltMonad ExecutionResult := do
  jolt_virtual_advice_load rd (advice.setWidth 64)
  let _ ← liftSail (execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SLLI)
  let _ ← liftSail (execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SRAI)
  pure RETIRE_SUCCESS

def execute_ADVICELW_inline (rd : regidx) (advice : BitVec 32) : SailM ExecutionResult := do
  wX_bits rd (advice.setWidth 64)
  let _ ← execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SLLI
  let _ ← execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SRAI
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_32 (advice : BitVec 32) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (32 : BitVec 6)) (32 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_32 advice

/-- Main theorem for `ADVICELW`: the inline Sail program collapses to the compact spec. -/
theorem execute_ADVICELW_inline_eq_spec (rd : regidx) (advice : BitVec 32)
    (hrd : rd ≠ regidx.Regidx 0) :
    execute_ADVICELW_inline rd advice = execute_ADVICELW rd advice := by
  simpa [execute_ADVICELW_inline, execute_ADVICELW] using
    execute_advice_inline_eq_spec_nonzero rd hrd (advice.setWidth 64)
      (sign_extend (m := 64) advice) (32 : BitVec 6)
      (advice_shift_sign_extend_32 advice)

theorem jolt_advicelw_eq_inline
    (rd : regidx) (advice : BitVec 32) (js : SailJoltState) :
    projectResult ((jolt_advicelw rd advice).run js) =
      (execute_ADVICELW_inline rd advice).run js.sail := by
  simpa [jolt_advicelw, jolt_virtual_advice_load, execute_ADVICELW_inline] using
    (projectResult_liftSail_seq3
      (wX_bits rd (advice.setWidth 64))
      (execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SLLI)
      (execute_SHIFTIOP (32 : BitVec 6) rd rd sop.SRAI)
      js)

end
