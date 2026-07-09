import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `XOR` equivalence statement. -/
def xorInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.XOR (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.XOR).run js.sail)

private abbrev op (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val ^^^ rs2_val

theorem xorInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    xorInstrEqSailStatement rs2 rs1 rd js h := by
  unfold xorInstrEqSailStatement
  simp only [execute_RTYPE, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read, h.rs2_read]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val h.rs2_val) js.sail
  simp only [h_write]
  simp only [JoltISA.execInstr]
  rw [bind_after_success_of_readSrc_xreg rs1 js h.rs1_val h.rs1_read]
  rw [bind_after_success_of_readSrc_xreg rs2 js h.rs2_val h.rs2_read]
  rw [bind_after_success_of_writeDst_xreg rd js _ s' h_write _]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op h.rs1_val h.rs2_val)
    h.linkedCSRs h_write

end Natives

end
