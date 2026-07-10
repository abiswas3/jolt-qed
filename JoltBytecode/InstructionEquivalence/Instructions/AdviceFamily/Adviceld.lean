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

private theorem execute_ADVICELD_reduces (rd : regidx) (advice : BitVec 64)
    (js : SailJoltState) :
    (execute_ADVICELD rd advice).run js.sail =
      .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd advice) := by
  unfold execute_ADVICELD
  obtain ⟨s', hwrite⟩ := wX_shape rd advice js.sail
  change
    ((wX_bits rd advice >>= fun _ =>
      pure RETIRE_SUCCESS : SailM ExecutionResult) js.sail) =
        .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd advice)
  simp only [bind, EStateM.bind, hwrite, pure, EStateM.pure]
  rw [wX_bits_eq_stateAfterWrite rd advice js.sail s' hwrite]

private theorem adviceldProgram_writesNoProtected
    (rd : regidx) (advice : BitVec 64) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.adviceldProgram rd advice) := by
  unfold JoltISA.adviceldProgram JoltISA.adviceLoadDstFor
    JoltISA.sideEffectingRdZeroDst
  split
  · simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg]
    simpa [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp0] using
      JoltISA.inlineTmp0_not_protected
  · simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg]

private theorem adviceldProgram_concrete_x0 (advice : BitVec 64)
    (js : SailJoltState) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.adviceldProgram (regidx.Regidx 0) advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = js.sail := by
  let vd := JoltISA.rdZeroRewriteVReg
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then advice else js.vregs r }
  have hvd : WritableVReg vd := by
    unfold vd JoltISA.rdZeroRewriteVReg WritableVReg
    decide
  have hload :
      (JoltISA.execInstr (.VirtualAdviceLoad (.vreg vd) advice)).run js =
        .ok RETIRE_SUCCESS js_load := by
    simpa [js_load, vd] using
      JoltISA.virtual_advice_load_run_vreg vd advice js hvd
  refine ⟨js_load, ?_, rfl⟩
  unfold JoltISA.adviceldProgram JoltISA.adviceLoadDstFor
    JoltISA.sideEffectingRdZeroDst
  rw [JoltISA.isX0_regidx_zero]
  simp only [↓reduceIte]
  rw [JoltISA.execProgram_instr_run_retire _ _ js js_load hload]
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- Program-level execution for `ADVICELD`. -/
theorem adviceldProgram_concrete (rd : regidx) (advice : BitVec 64)
    (js : SailJoltState)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd advice := by
  have hx0 : JoltISA.isX0 rd = false :=
    JoltISA.isX0_eq_false_of_ne_zero hrd
  obtain ⟨js_load, hload_sail, _hload_vregs, hload_run⟩ :=
    JoltISA.exists_state_after_virtual_advice_load_run_xreg rd advice js
  refine ⟨js_load, ?_, hload_sail⟩
  unfold JoltISA.adviceldProgram JoltISA.adviceLoadDstFor
    JoltISA.sideEffectingRdZeroDst
  rw [hx0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [JoltISA.execProgram_instr_run_retire _ _ js js_load hload_run]
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]

/-- Main program-level theorem for `ADVICELD`. -/
private theorem adviceldProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js) =
      (execute_ADVICELD rd advice).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      adviceldProgram_concrete_x0 advice js
    rw [hjolt, execute_ADVICELD_reduces]
    simp only [projectResult, project]
    rw [hjolt_sail, stateAfterWrite_regidx_zero]
  · obtain ⟨js', hjolt, hjolt_sail⟩ :=
      adviceldProgram_concrete rd advice js hrd
    rw [hjolt, execute_ADVICELD_reduces]
    simp only [projectResult, project]
    rw [hjolt_sail]

/-- Main program-level theorem for `ADVICELD`. -/
theorem adviceldProgram_eq_sail
    (rd : regidx) (advice : BitVec 64) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.adviceldProgram rd advice)).run js)
      ((execute_ADVICELD rd advice).run js.sail) := by
  exact programMatchesSailWithProtectedFrame_of_projectResult_eq
    (adviceldProgram_project_eq_sail rd advice js)
    (adviceldProgram_writesNoProtected rd advice)

end
