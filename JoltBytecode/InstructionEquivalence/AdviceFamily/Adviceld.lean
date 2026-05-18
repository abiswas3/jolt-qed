import JoltBytecode.InstructionEquivalence.AdviceFamily.Advice

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Sail-side spec for `ADVICELD`: write the advised dword to `rd`. -/
def execute_ADVICELD (rd : regidx) (advice : BitVec 64) : SailM ExecutionResult := do
  wX_bits rd advice
  pure RETIRE_SUCCESS

/-- Jolt inline for `ADVICELD`: `VirtualAdviceLoad rd, 8`. -/
def jolt_adviceld (rd : regidx) (advice : BitVec 64) : JoltMonad ExecutionResult := do
  jolt_virtual_advice_load rd advice
  pure RETIRE_SUCCESS

theorem jolt_adviceld_eq_inline
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    projectResult ((jolt_adviceld rd advice).run js) =
      (execute_ADVICELD rd advice).run js.sail := by
  simpa [jolt_adviceld, jolt_virtual_advice_load, execute_ADVICELD] using
    (projectResult_liftSail_seq1 (wX_bits rd advice) js)

end
