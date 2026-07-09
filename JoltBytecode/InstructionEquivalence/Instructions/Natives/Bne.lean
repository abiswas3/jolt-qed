import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Blt

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

-- TODO:
/-- Main native `BNE` equivalence statement. -/
def bneInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.BNE (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BNE).run js.sail)

theorem bneInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    bneInstrEqSailStatement imm rs2 rs1 js h := by
  unfold bneInstrEqSailStatement
  -- RHS
  simp only [execute_BTYPE]
  simp only [EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  -- LHS
  simp only [JoltISA.execInstr]
  rw [bind_after_success_of_readSrc_xreg rs1 js h.rs1_val h.rs1_read _]
  rw [bind_after_success_of_readSrc_xreg rs2 js h.rs2_val h.rs2_read _]
  by_cases h_ne : h.rs1_val ≠ h.rs2_val
  · -- taken
    simp [h_ne]
    rw [← Projection.liftSail_bind]
    exact Projection.systemProjectResult_liftSail_eq_of_preservesSystemProjectRegs
      h.linkedCSRs
      (branchJump_preservesSystemProjectRegs imm js)
  · -- not taken
    have h_eq : h.rs1_val = h.rs2_val := by
      by_contra h_eq
      exact h_ne h_eq
    simp [h_eq]
    exact Projection.systemProjectResult_pure_retire js h.linkedCSRs

end Natives

end
