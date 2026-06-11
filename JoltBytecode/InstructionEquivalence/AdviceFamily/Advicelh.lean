import JoltBytecode.InstructionEquivalence.AdviceFamily.Advice
import JoltBytecode.JoltISA.Expansions.Advice
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.ALU
import JoltBytecode.JoltISA.Semantics.Instructions

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-- Reference semantics for the Jolt-only `ADVICELH`: write the sign-extended
advised halfword to `rd`. -/
def execute_ADVICELH (rd : regidx) (advice : BitVec 16) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_16 (advice : BitVec 16) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (48 : BitVec 6)) (48 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_16 advice

private lemma advicelh_final_value (advice : BitVec 16) :
    jolt_virtual_srai_value
        (shift_bits_left (advice.setWidth 64) (48 : BitVec 6))
        (JoltISA.sraiBitmask (48 : BitVec 6)) =
      sign_extend (m := 64) advice := by
  rw [JoltISA.srai_block_value_eq]
  exact advice_shift_sign_extend_16 advice

theorem advicelhProgram_concrete (rd : regidx) (advice : BitVec 16)
    (js : SailJoltState)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.advicelhProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sign_extend (m := 64) advice) := by
  let advice64 := advice.setWidth 64

  obtain ⟨js_afterAdvice, h_advice_sail, _h_advice_vregs,
      h_advice_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_advice_load_run_xreg rd advice64 js

  have h_read_afterAdvice :
      rX_bits rd js_afterAdvice.sail = .ok advice64 js_afterAdvice.sail := by
    rw [h_advice_sail]
    exact rX_after_stateAfterWrite rd advice64 js.sail hrd

  obtain ⟨js_afterSlli, _h_slli_read, h_slli_sail, _h_slli_vregs,
      h_slli_tail⟩ :=
    JoltISA.exists_state_after_slli_block_run_xreg_xreg
      rd rd (48 : BitVec 6) js_afterAdvice advice64 h_read_afterAdvice

  let shifted := shift_bits_left advice64 (48 : BitVec 6)

  have h_read_afterSlli :
      rX_bits rd js_afterSlli.sail = .ok shifted js_afterSlli.sail := by
    rw [h_slli_sail]
    exact rX_after_stateAfterWrite rd shifted js_afterAdvice.sail hrd

  obtain ⟨js_afterSrai, _h_srai_read, h_srai_sail, h_srai_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srai_run_xreg_xreg
      rd rd (JoltISA.sraiBitmask (48 : BitVec 6)) js_afterSlli shifted
      h_read_afterSlli

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.advicelhProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js_afterSrai := by
    unfold JoltISA.advicelhProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAdvice
      h_advice_succeeds]
    rw [h_slli_tail
      (.instr
        (.VirtualSRAI (.xreg rd) (.xreg rd) (JoltISA.sraiBitmask (48 : BitVec 6)))
        (.done RETIRE_SUCCESS))]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSlli js_afterSrai
      h_srai_succeeds]
    rfl

  refine ⟨js_afterSrai, h_program_succeeds, ?_⟩

  have h_value :
      jolt_virtual_srai_value shifted
          (JoltISA.sraiBitmask (48 : BitVec 6)) =
        sign_extend (m := 64) advice := by
    simpa [shifted, advice64] using advicelh_final_value advice

  rw [h_srai_sail, h_value, h_slli_sail, h_advice_sail]
  rw [stateAfterWrite_stateAfterWrite]
  rw [stateAfterWrite_stateAfterWrite]

theorem advicelhProgram_eq_sail
    (rd : regidx) (advice : BitVec 16) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.advicelhProgram rd advice)).run js) =
      (execute_ADVICELH rd advice).run js.sail := by
  by_cases hrd_zero : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.advicelhProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    unfold execute_ADVICELH
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    rw [wX_bits_regidx_zero]

  obtain ⟨js', h_program_succeeds, h_final_sail⟩ :=
    advicelhProgram_concrete rd advice js hrd_zero

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  simp only [execute_ADVICELH, EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (sign_extend (m := 64) advice) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sign_extend (m := 64) advice) js.sail s'
    h_write).symm

end
