import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualSRA instruction semantics

Run lemmas for the Jolt ISA `VirtualSRA` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSRA` from a real value and a virtual bitmask to a real destination
is the arithmetic sibling of `virtual_srl_run_xreg_xreg_vreg`. -/
theorem virtual_sra_run_xreg_xreg_vreg (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_sra_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRA (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRA` from a real value and a virtual bitmask to a real destination,
with the output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_sra_run_xreg_xreg_vreg
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSRA (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_sra_value x (js.vregs vbitmask)) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_sra_value x (js.vregs vbitmask)) js.sail
  exact ⟨s', virtual_sra_run_xreg_xreg_vreg rd rs vbitmask js x s' h hw, hw⟩

/-- `VirtualSRA` can read both its value and its bitmask from virtual registers
before writing the result through Sail. -/
theorem virtual_sra_run_xreg_vreg_vreg (rd : regidx) (vvalue vbitmask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask))
      js.sail = .ok () s') :
    (execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRA` from two virtual sources to a real destination, with the
output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_sra_run_xreg_vreg_vreg
    (rd : regidx) (vvalue vbitmask : VReg) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask))
        js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) js.sail
  exact ⟨s', virtual_sra_run_xreg_vreg_vreg rd vvalue vbitmask js s' hw, hw⟩

end JoltISA

end
