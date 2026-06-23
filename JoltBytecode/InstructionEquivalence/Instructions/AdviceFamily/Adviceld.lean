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
  obtain ⟨js_afterAdvice, h_advice_sail, _h_advice_vregs,
      h_advice_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_advice_load_run_xreg rd advice js

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js_afterAdvice := by
    unfold JoltISA.adviceldProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAdvice
      h_advice_succeeds]
    rfl

  exact ⟨js_afterAdvice, h_program_succeeds, h_advice_sail⟩

/-- Main program-level theorem for `ADVICELD`. -/
private theorem adviceldProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js) =
      (execute_ADVICELD rd advice).run js.sail := by
  by_cases hrd_zero : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.adviceldProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    unfold execute_ADVICELD
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    rw [wX_bits_regidx_zero]

  obtain ⟨js', h_program_succeeds, h_final_sail⟩ :=
    adviceldProgram_concrete rd advice js hrd_zero

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  simp only [execute_ADVICELD, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd advice js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd advice js.sail s' h_write).symm

/-- Main program-level theorem for `ADVICELD`. -/
theorem adviceldProgram_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js)
      ((execute_ADVICELD rd advice).run js.sail) := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · exact adviceldProgram_project_eq_sail rd advice js
  · unfold JoltISA.adviceldProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]

end
