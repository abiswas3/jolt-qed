import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualSRL instruction semantics

Run lemmas for the Jolt ISA `VirtualSRL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRL` from a real value and a virtual bitmask to a real destination
is the two-instruction `SRL` program's final write. -/
theorem virtual_srl_run_xreg_xreg_vreg (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRL` from a real value and a virtual bitmask to a real destination,
with the output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_srl_run_xreg_xreg_vreg
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail
  exact ⟨s', virtual_srl_run_xreg_xreg_vreg rd rs vbitmask js x s' h hw, hw⟩

/-- `VirtualSRL` can read both its value and its bitmask from virtual registers
before writing the result to a real destination. -/
theorem virtual_srl_run_xreg_vreg_vreg (rd : regidx) (vvalue vbitmask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask))
      js.sail = .ok () s') :
    (execInstr (.VirtualSRL (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRL` from two virtual sources to a real destination, with the
output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_srl_run_xreg_vreg_vreg
    (rd : regidx) (vvalue vbitmask : VReg) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRL (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask))
        js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask)) js.sail
  exact ⟨s', virtual_srl_run_xreg_vreg_vreg rd vvalue vbitmask js s' hw, hw⟩

end JoltISA

end
