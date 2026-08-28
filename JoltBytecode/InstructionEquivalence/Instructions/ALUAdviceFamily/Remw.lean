import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMW program equivalence

The Rust expansion now takes one advice value: the magnitude of the signed
word quotient. It computes and sign-corrects the architectural remainder.
-/

def remwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotientMagnitude = remw_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail

def remwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_remw_value h.rs1_val h.rs2_val false)

def remwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remwProgramCompletenessStatement rs2 rs1 rd quotientMagnitude js h ∧
  remwProgramSoundnessStatement rs2 rs1 rd quotientMagnitude js h

theorem remwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remwProgramEqSailStatement rs2 rs1 rd quotientMagnitude js h := by
  sorry

end
