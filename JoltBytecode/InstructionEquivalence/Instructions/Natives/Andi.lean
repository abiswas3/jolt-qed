import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ANDI` equivalence statement. -/
def andiInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ANDI (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ITYPE imm rs1 rd iop.ANDI).run js.sail)

abbrev op (rs1_val : BitVec 64) (imm: BitVec 12): BitVec 64 :=
  rs1_val &&& sign_extend imm

theorem andiInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    andiInstrEqSailStatement imm rs1 rd js h := by
  unfold andiInstrEqSailStatement
  -- RHS 
  simp only [execute_ITYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail  
  simp only [pure, EStateM.pure, h_write] 
  -- LHS 
  simp only [JoltISA.execInstr]
  -- being lazy and letting lean infer all the args
  rw [bind_after_success_of_readSrc_xreg rs1 js h.rs1_val h.rs1_read]
  rw [bind_after_success_of_writeDst_xreg rd js (op h.rs1_val imm) s' h_write _] -- write succeeds and the value is interpreted. 
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val imm)
    h.linkedCSRs h_write
end Natives

end
