import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualMULI instruction semantics

Run lemmas for the Jolt ISA `VirtualMULI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualMULI` from a real source to a real destination multiplies the
source by the encoded immediate and writes the result through Sail. -/
theorem virtual_muli_run_xreg_xreg (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_muli_value x imm) js.sail = .ok () s') :
    (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualMULI` from a real source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_muli_run_xreg_xreg (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_muli_value x imm) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_muli_value x imm) js.sail
  exact ⟨s', virtual_muli_run_xreg_xreg rd rs1 imm js x s' h hw, hw⟩

end JoltISA

end
