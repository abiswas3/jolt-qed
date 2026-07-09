import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LUI

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `LUI` equivalence statement. -/
def luiInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execLUI imm rd).run js) =
    ((execute_UTYPE imm rd uop.LUI).run js.sail)

abbrev op (imm : BitVec 20) : BitVec 64 :=
  JoltISA.luiValue imm

/-- Native `LUI` writes the normalized immediate in both Jolt and Sail. -/
theorem luiInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    luiInstrEqSailStatement imm rd js h := by
  unfold luiInstrEqSailStatement
  -- RHS
  simp only [execute_UTYPE, EStateM.run, bind, EStateM.bind]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (op imm) js.sail
  have h_write_sail :
      wX_bits rd (sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12))) js.sail =
        .ok () s' := by
    unfold op JoltISA.luiValue at h_write
    exact h_write
  simp only [h_write_sail]

  -- LHS
  simp only [JoltISA.execLUI, JoltISA.execInstr]
  rw [bind_after_success_of_writeDst_xreg rd js _ s' h_write _]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op imm)
    h.linkedCSRs h_write
end Natives

end
