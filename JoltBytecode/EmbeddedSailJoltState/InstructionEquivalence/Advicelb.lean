import JoltBytecode.EmbeddedSailJoltState.Advice

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Sail-side spec for `ADVICELB`: write the sign-extended advised byte to `rd`. -/
def execute_ADVICELB (rd : regidx) (advice : BitVec 8) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

/-- Jolt inline for `ADVICELB`: advice load, then `SLLI 56`, then `SRAI 56`. -/
def jolt_advicelb (rd : regidx) (advice : BitVec 8) : JoltMonad ExecutionResult := do
  jolt_virtual_advice_load rd (advice.setWidth 64)
  let _ ← liftSail (execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SLLI)
  let _ ← liftSail (execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SRAI)
  pure RETIRE_SUCCESS

def execute_ADVICELB_inline (rd : regidx) (advice : BitVec 8) : SailM ExecutionResult := do
  wX_bits rd (advice.setWidth 64)
  let _ ← execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SLLI
  let _ ← execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SRAI
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_8 (advice : BitVec 8) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (56 : BitVec 6)) (56 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_8 advice

/-- Main theorem for `ADVICELB`: the inline Sail program collapses to the compact spec. -/
theorem execute_ADVICELB_inline_eq_spec (rd : regidx) (advice : BitVec 8)
    (hrd : rd ≠ regidx.Regidx 0) :
    execute_ADVICELB_inline rd advice = execute_ADVICELB rd advice := by
  simpa [execute_ADVICELB_inline, execute_ADVICELB] using
    execute_advice_inline_eq_spec_nonzero rd hrd (advice.setWidth 64)
      (sign_extend (m := 64) advice) (56 : BitVec 6)
      (advice_shift_sign_extend_8 advice)

theorem jolt_advicelb_eq_inline
    (rd : regidx) (advice : BitVec 8) (js : SailJoltState) :
    projectResult ((jolt_advicelb rd advice).run js) =
      (execute_ADVICELB_inline rd advice).run js.sail := by
  simpa [jolt_advicelb, jolt_virtual_advice_load, execute_ADVICELB_inline] using
    (projectResult_liftSail_seq3
      (wX_bits rd (advice.setWidth 64))
      (execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SLLI)
      (execute_SHIFTIOP (56 : BitVec 6) rd rd sop.SRAI)
      js)

end
