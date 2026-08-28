import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVW program equivalence

The Rust expansion now takes one quotient advice value. The public statement
therefore targets the generated expansion directly.
-/

def divwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = divw_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.divwProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIVW rs2 rs1 rd false).run js.sail

def divwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.divwProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = divw_advice_value h.rs1_val h.rs2_val

def divwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divwProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divwProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divwProgramEqSailStatement rs2 rs1 rd quotient js h := by
  sorry

end
