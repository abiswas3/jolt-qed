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

/-- Reference semantics for the Jolt-only `ADVICELW`: write the sign-extended
advised word to `rd`. -/
def execute_ADVICELW (rd : regidx) (advice : BitVec 32) : SailM ExecutionResult := do
  wX_bits rd (sign_extend (m := 64) advice)
  pure RETIRE_SUCCESS

private lemma advice_shift_sign_extend_32 (advice : BitVec 32) :
    shift_bits_right_arith (shift_bits_left (advice.setWidth 64) (32 : BitVec 6)) (32 : BitVec 6) =
      sign_extend (m := 64) advice := by
  unfold shift_bits_left shift_bits_right_arith sign_extend
  simpa using sshiftRight_slli_signExtend_32 advice

private lemma advicelw_final_value (advice : BitVec 32) :
    jolt_virtual_srai_value
        (shift_bits_left (advice.setWidth 64) (32 : BitVec 6))
        (JoltISA.sraiBitmask (32 : BitVec 6)) =
      sign_extend (m := 64) advice := by
  rw [JoltISA.srai_block_value_eq]
  exact advice_shift_sign_extend_32 advice

theorem advicelwProgram_concrete (rd : regidx) (advice : BitVec 32)
    (js : SailJoltState)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.advicelwProgram rd advice)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sign_extend (m := 64) advice) := by
  sorry

private theorem advicelwProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 32) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.advicelwProgram rd advice)).run js) =
      (execute_ADVICELW rd advice).run js.sail := by
  sorry

theorem advicelwProgram_eq_sail
    (rd : regidx) (advice : BitVec 32) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.advicelwProgram rd advice)).run js)
      ((execute_ADVICELW rd advice).run js.sail) := by
  sorry

end
