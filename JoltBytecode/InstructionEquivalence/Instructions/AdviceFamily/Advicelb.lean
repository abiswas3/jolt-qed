import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Advice
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.Advice
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Reference semantics for the Jolt-only `ADVICELB`: write the sign-extended
advised byte to `rd`. -/
def execute_ADVICELB (rd : regidx) (advice : BitVec 8) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_8 (advice : BitVec 8) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (56 : BitVec 6)) (56 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_8 advice

private lemma advicelb_final_value (advice : BitVec 8) :
    jolt_virtual_srai_value
        (shift_bits_left (advice.setWidth 64) (56 : BitVec 6))
        (JoltISA.sraiBitmask (56 : BitVec 6)) =
      sign_extend (m := 64) advice := by
  rw [JoltISA.srai_block_value_eq]
  exact advice_shift_sign_extend_8 advice

private theorem execute_ADVICELB_reduces (rd : regidx) (advice : BitVec 8)
    (js : SailJoltState) :
    (execute_ADVICELB rd advice).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sign_extend (m := 64) advice)) := by
  unfold execute_ADVICELB
  obtain ⟨s', hwrite⟩ :=
    wX_shape rd (sign_extend (m := 64) advice) js.sail
  change
    ((wX_bits rd (sign_extend (m := 64) advice) >>= fun _ =>
      pure RETIRE_SUCCESS : SailM ExecutionResult) js.sail) =
        .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd (sign_extend (m := 64) advice))
  simp only [bind, EStateM.bind, hwrite, pure, EStateM.pure]
  rw [wX_bits_eq_stateAfterWrite rd (sign_extend (m := 64) advice)
    js.sail s' hwrite]

private theorem advicelbProgram_writesNoProtected
    (rd : regidx) (advice : BitVec 8) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.advicelbProgram rd advice) := by
  unfold JoltISA.advicelbProgram JoltISA.adviceLoadDstFor
    JoltISA.adviceLoadSrcFor JoltISA.sideEffectingRdZeroDst JoltISA.slliBlock
  split
  · simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg]
    simpa [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp0] using
      JoltISA.inlineTmp0_not_protected
  · simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg]

private theorem advicelbProgram_concrete_x0 (advice : BitVec 8)
    (js : SailJoltState) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.advicelbProgram (regidx.Regidx 0) advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = js.sail := by
  let vd := JoltISA.rdZeroRewriteVReg
  let js_load : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then advice.setWidth 64 else js.vregs r }
  have hvd : WritableVReg vd := by
    unfold vd JoltISA.rdZeroRewriteVReg WritableVReg
    decide
  have hload :
      (JoltISA.execInstr (.VirtualAdviceLoad (.vreg vd) (advice.setWidth 64))).run js =
        .ok RETIRE_SUCCESS js_load := by
    simpa [js_load, vd] using
      JoltISA.virtual_advice_load_run_vreg vd (advice.setWidth 64) js hvd
  obtain ⟨js_shift, hshift_sail, _hshift_vd, _hshift_pres, hshift_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_vreg
      vd vd (56 : BitVec 6) js_load hvd
  obtain ⟨js_final, hsrai_run, _hsrai_vd, _hsrai_pres, hsrai_sail⟩ :=
    JoltISA.srai_block_run_vreg_vreg_ex vd vd (56 : BitVec 6) js_shift hvd
  refine ⟨js_final, ?_, ?_⟩
  · unfold JoltISA.advicelbProgram JoltISA.adviceLoadDstFor
      JoltISA.adviceLoadSrcFor JoltISA.sideEffectingRdZeroDst
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_load hload]
    rw [hshift_run]
    change
      (JoltISA.execProgram
        (JoltISA.sraiBlock (.vreg JoltISA.rdZeroRewriteVReg)
          (.vreg JoltISA.rdZeroRewriteVReg) (56 : BitVec 6)
          (.done RETIRE_SUCCESS))).run js_shift =
        .ok RETIRE_SUCCESS js_final
    rw [hsrai_run]
    simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]
  · rw [hsrai_sail, hshift_sail]

/-- Program-level execution for `ADVICELB`.

The left-hand side is the actual final-row Jolt ISA program:
`VirtualAdviceLoad`, lowered `SLLI 56`, and final-row `VirtualSRAI 56`.
-/
theorem advicelbProgram_concrete (rd : regidx) (advice : BitVec 8)
    (js : SailJoltState)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.advicelbProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sign_extend (m := 64) advice) := by
  have hx0 : JoltISA.isX0 rd = false :=
    JoltISA.isX0_eq_false_of_ne_zero hrd
  obtain ⟨js_load, hload_sail, hload_vregs, hload_run⟩ :=
    JoltISA.exists_state_after_virtual_advice_load_run_xreg
      rd (advice.setWidth 64) js
  have hread_after_load :
      rX_bits rd js_load.sail = .ok (advice.setWidth 64) js_load.sail := by
    rw [hload_sail]
    exact rX_after_stateAfterWrite rd (advice.setWidth 64) js.sail hrd
  obtain ⟨js_shift, _hread_slli, hshift_sail, _hshift_vregs, hshift_run⟩ :=
    JoltISA.exists_state_after_slli_block_run_xreg_xreg
      rd rd (56 : BitVec 6) js_load (advice.setWidth 64) hread_after_load
  have hread_after_shift :
      rX_bits rd js_shift.sail =
        .ok (shift_bits_left (advice.setWidth 64) (56 : BitVec 6))
          js_shift.sail := by
    rw [hshift_sail]
    exact rX_after_stateAfterWrite rd
      (shift_bits_left (advice.setWidth 64) (56 : BitVec 6))
      js_load.sail hrd
  obtain ⟨js_final, _hread_srai, hsrai_sail, hsrai_run⟩ :=
    JoltISA.exists_state_after_virtual_srai_run_xreg_xreg
      rd rd (JoltISA.sraiBitmask (56 : BitVec 6)) js_shift
      (shift_bits_left (advice.setWidth 64) (56 : BitVec 6))
      hread_after_shift
  refine ⟨js_final, ?_, ?_⟩
  · unfold JoltISA.advicelbProgram JoltISA.adviceLoadDstFor
      JoltISA.adviceLoadSrcFor JoltISA.sideEffectingRdZeroDst
    rw [hx0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_load hload_run]
    rw [hshift_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_final hsrai_run]
    simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure]
  · rw [hsrai_sail, hshift_sail, hload_sail]
    rw [advicelb_final_value]
    rw [stateAfterWrite_stateAfterWrite]
    rw [stateAfterWrite_stateAfterWrite]

/-- Main program-level theorem for `ADVICELB`. -/
private theorem advicelbProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 8) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.advicelbProgram rd advice)).run js) =
      (execute_ADVICELB rd advice).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      advicelbProgram_concrete_x0 advice js
    rw [hjolt, execute_ADVICELB_reduces]
    simp only [projectResult, project]
    rw [hjolt_sail, stateAfterWrite_regidx_zero]
  · obtain ⟨js', hjolt, hjolt_sail⟩ :=
      advicelbProgram_concrete rd advice js hrd
    rw [hjolt, execute_ADVICELB_reduces]
    simp only [projectResult, project]
    rw [hjolt_sail]

/-- Main program-level theorem for `ADVICELB`. -/
theorem advicelbProgram_eq_sail
    (rd : regidx) (advice : BitVec 8) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.advicelbProgram rd advice)).run js)
      ((execute_ADVICELB rd advice).run js.sail) := by
  exact programMatchesSailWithProtectedFrame_of_projectResult_eq
    (advicelbProgram_project_eq_sail rd advice js)
    (advicelbProgram_writesNoProtected rd advice)

end
