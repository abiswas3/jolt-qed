import JoltBytecode.InstructionEquivalence.Semantics.Lemmas

/-!
# VirtualMovsign instruction semantics

Run lemmas for the Jolt ISA `VirtualMovsign` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualMovsign` from a real register to a virtual register reads the real
source, writes the sign mask to the virtual destination, and leaves the Sail
state unchanged. -/
theorem movsign_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualMovsign (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_movsign_value x) js hvd

/-- `VirtualMovsign` from a virtual register to a virtual register writes the
sign mask of the virtual source and leaves the Sail state unchanged. -/
theorem movsign_run_vreg_vreg (vd vs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualMovsign (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_movsign_value (js.vregs vs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (jolt_movsign_value (js.vregs vs)) js hvd

/-- `VirtualMovsign` from a real source to a virtual destination, packaged as
an instruction step from a known base Sail state. -/
theorem exists_state_after_movsign_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState)
    (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_movsign_value x ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualMovsign (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r }
  refine ⟨js', h_read_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using movsign_run_vreg_xreg vd rs js x h_read_current hvd

/-- `VirtualMovsign` from a virtual source to a virtual destination, packaged
as an instruction step from a known virtual-source value. -/
theorem exists_state_after_movsign_run_vreg_vreg
    (vd vs : VReg) (js : SailJoltState) (x : BitVec 64)
    (h_source : js.vregs vs = x)
    (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = jolt_movsign_value x ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualMovsign (.vreg vd) (.vreg vs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_movsign_value (js.vregs vs) else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_source]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using movsign_run_vreg_vreg vd vs js hvd

end JoltISA

end
