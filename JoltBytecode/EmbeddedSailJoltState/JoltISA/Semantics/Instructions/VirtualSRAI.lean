import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualSRAI instruction semantics

Run lemmas for the Jolt ISA `VirtualSRAI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRAI` from a real source to a real destination writes the arithmetic
right shift selected by the encoded immediate bitmask. -/
theorem execInstr_virtualSRAI_xreg_xreg_run (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srai_value x bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualSRAI` from a real source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem execInstr_virtualSRAI_xreg_xreg_run_of_read (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srai_value x bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srai_value x bitmask) js.sail
  exact ⟨s', execInstr_virtualSRAI_xreg_xreg_run rd rs bitmask js x s' h hw, hw⟩

/-- `VirtualSRAI` can consume a value from a virtual register and write the
arithmetic shift result to a real destination. -/
theorem execInstr_virtualSRAI_vreg_xreg_run (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRAI` from a virtual source to a real destination, with the output
state chosen by the instruction lemma. -/
theorem execInstr_virtualSRAI_vreg_xreg_run_of_vreg (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail
  exact ⟨s', execInstr_virtualSRAI_vreg_xreg_run rd vs bitmask js s' hw, hw⟩

end JoltISA

end
