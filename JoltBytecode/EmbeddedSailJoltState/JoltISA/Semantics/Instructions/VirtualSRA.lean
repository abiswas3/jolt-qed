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

/-- `VirtualSRA` from a real source and a virtual bitmask to a real destination,
with the output Sail state exposed as the architectural write performed by the
instruction. -/
theorem exists_jolt_state_after_virtual_sra_run_xreg_xreg_vreg
    (rd rs : regidx) (vbitmask : VReg) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_virtual_sra_value x (js.vregs vbitmask)) ∧
      (execInstr (.VirtualSRA (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_run, h_write⟩ :=
    exists_state_after_virtual_sra_run_xreg_xreg_vreg rd rs vbitmask js x h
  have h_sail_after_sra :
      s' = stateAfterWrite js.sail rd (jolt_virtual_sra_value x (js.vregs vbitmask)) :=
    wX_bits_eq_stateAfterWrite rd (jolt_virtual_sra_value x (js.vregs vbitmask))
      js.sail s' h_write
  exact ⟨{ sail := s', vregs := js.vregs }, h, h_sail_after_sra, h_run⟩

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
output Sail state exposed as the architectural write performed by the
instruction. -/
theorem exists_state_after_virtual_sra_run_xreg_vreg_vreg
    (rd : regidx) (vvalue vbitmask : VReg) (js : SailJoltState) :
    ∃ js',
      js'.sail = stateAfterWrite js.sail rd
        (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) ∧
      (execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) js.sail
  have h_sail_after_sra :
      s' = stateAfterWrite js.sail rd
        (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) :=
    wX_bits_eq_stateAfterWrite rd
      (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask)) js.sail s' hw
  exact ⟨{ sail := s', vregs := js.vregs },
    h_sail_after_sra,
    virtual_sra_run_xreg_vreg_vreg rd vvalue vbitmask js s' hw⟩

end JoltISA

end
