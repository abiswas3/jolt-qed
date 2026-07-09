import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Advice
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.Advice
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Reference semantics for the Jolt-only `ADVICELD`: write the advised dword to
`rd`. -/
def execute_ADVICELD (rd : regidx) (advice : BitVec 64) : SailM ExecutionResult := do
  wX_bits rd advice
  pure RETIRE_SUCCESS

/-- Program-level execution for `ADVICELD`. -/
theorem adviceldProgram_concrete (rd : regidx) (advice : BitVec 64)
    (js : SailJoltState)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd advice := by
  sorry

/-- Main program-level theorem for `ADVICELD`. -/
private theorem adviceldProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js) =
      (execute_ADVICELD rd advice).run js.sail := by
  sorry

/-- Main program-level theorem for `ADVICELD`. -/
theorem adviceldProgram_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js)
      ((execute_ADVICELD rd advice).run js.sail) := by
  sorry

end
