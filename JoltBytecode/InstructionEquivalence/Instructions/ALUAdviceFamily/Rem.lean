import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REM program equivalence

The Rust expansion now takes one advice value: the magnitude of the quotient.
It computes and sign-corrects the architectural remainder itself.
-/

def remProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotientMagnitude = rem_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)).run js) =
    (execute_REM rs2 rs1 rd false).run js.sail

def remProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_rem_value h.rs1_val h.rs2_val false)

def remProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remProgramCompletenessStatement rs2 rs1 rd quotientMagnitude js h ∧
  remProgramSoundnessStatement rs2 rs1 rd quotientMagnitude js h

theorem remProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remProgramEqSailStatement rs2 rs1 rd quotientMagnitude js h := by
  sorry

end
