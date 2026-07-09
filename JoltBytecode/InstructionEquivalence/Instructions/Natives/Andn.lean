import JoltBytecode.JoltISA.Core
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ANDN` equivalence statement. -/
def andnInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_ZBB_RTYPE rs2 rs1 rd brop_zbb.ANDN).run js.sail)


private abbrev op (rs1_val rs2_val : BitVec 64): BitVec 64 :=
  rs1_val &&& Complement.complement rs2_val 


theorem andnInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    andnInstrEqSailStatement rs2 rs1 rd js h := by
  unfold andnInstrEqSailStatement 
  -- parsing the RHS of the main theorem statement 
  simp only [execute_ZBB_RTYPE] -- Tell the giant match block we are doing ANDN
  simp only [EStateM.run_bind] -- Go from do notation to nested matches
  simp only [EStateM.run]
  simp only [h.rs1_read, h.rs2_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]
  -- parsing the LHS (Jolt side)
  simp only [JoltISA.execInstr]
  rw [bind_after_success_of_readSrc_xreg rs1 js h.rs1_val h.rs1_read]
  rw [bind_after_success_of_readSrc_xreg rs2 js h.rs2_val h.rs2_read]
  rw [bind_after_success_of_writeDst_xreg rd js _ s' h_write _]
  -- Use the System Project helper 
  -- (NOTE: this helper proof quality  is not super clean but we will get to that later)
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write


end Natives

end
