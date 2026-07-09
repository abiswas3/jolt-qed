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
  sorry

/-- Main program-level theorem for `ADVICELB`. -/
private theorem advicelbProgram_project_eq_sail
    (rd : regidx) (advice : BitVec 8) (js : SailJoltState) :
    projectResult ((JoltISA.execProgram (JoltISA.advicelbProgram rd advice)).run js) =
      (execute_ADVICELB rd advice).run js.sail := by
  sorry

/-- Main program-level theorem for `ADVICELB`. -/
theorem advicelbProgram_eq_sail
    (rd : regidx) (advice : BitVec 8) (js : SailJoltState) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.advicelbProgram rd advice)).run js)
      ((execute_ADVICELB rd advice).run js.sail) := by
  sorry

end
