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
  sorry

private theorem advicelhProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 16) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.advicelhProgram rd advice)).run js) =
      (execute_ADVICELH rd advice).run js.sail := by
  sorry

theorem advicelhProgram_eq_sail
    (rd : regidx) (advice : BitVec 16) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.advicelhProgram rd advice)).run js)
      ((execute_ADVICELH rd advice).run js.sail) := by
  sorry

end
