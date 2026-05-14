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
is the arithmetic sibling of `execInstr_virtualSRL_xreg_vreg_xreg_run`. -/
theorem execInstr_virtualSRA_xreg_vreg_xreg_run (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_sra_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRA (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRA` can read both its value and its bitmask from virtual registers
before writing the result through Sail. -/
theorem execInstr_virtualSRA_vreg_vreg_xreg_run (rd : regidx) (vvalue vbitmask : VReg)
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
theorem execInstr_virtualSRA_vreg_vreg_xreg_run_of_vregs
    (rd : regidx) (vvalue vbitmask : VReg) (js : SailJoltState) :
    ∃ s',
      (execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask))
        js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) js.sail
  exact ⟨s', execInstr_virtualSRA_vreg_vreg_xreg_run rd vvalue vbitmask js s' hw, hw⟩

end JoltISA

end
