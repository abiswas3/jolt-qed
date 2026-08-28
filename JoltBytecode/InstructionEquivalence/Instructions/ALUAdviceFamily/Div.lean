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
# DIV program equivalence

The Rust expansion now takes one quotient advice value. The old handwritten
two-advice expansion and its proof decomposition are intentionally not used by
this public statement.
-/

def divProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = sail_div_value h.rs1_val h.rs2_val false →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.divProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail

def divProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.divProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = sail_div_value h.rs1_val h.rs2_val false

def divProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divProgramEqSailStatement rs2 rs1 rd quotient js h := by
  sorry

end
