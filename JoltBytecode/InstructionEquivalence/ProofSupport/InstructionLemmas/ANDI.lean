import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# ANDI instruction semantics

Run lemmas for the Jolt ISA `ANDI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ANDI` on virtual registers reads the virtual source, writes the masked
value to the virtual destination, and leaves the Sail state unchanged. -/
theorem andi_run_vreg_vreg (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.ANDI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (js.vregs vs &&& sign_extend (m := 64) imm) js hvd

/-- `ANDI` from a virtual source to a virtual destination, packaged as an
instruction step from a known virtual-source value. -/
theorem exists_state_after_andi_run_vreg_vreg
    (vd vs : VReg) (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hvd : WritableVReg vd)
    (h_value : js.vregs vs = x) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x &&& sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.ANDI (.vreg vd) (.vreg vs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm
        else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_value]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using andi_run_vreg_vreg vd vs imm js hvd

/-- `ANDI` from a real source to a virtual destination masks the source value
and leaves Sail unchanged. -/
theorem andi_run_vreg_xreg (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.ANDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (x &&& sign_extend (m := 64) imm) js hvd

/-- `ANDI` from a real source to a virtual destination, packaged as an
instruction step. The source read may be supplied from a known unchanged Sail
state, which is the common shape after earlier virtual-register writes. -/
theorem exists_state_after_andi_run_vreg_xreg_of_sail_eq
    (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = x &&& sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.ANDI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r }
  refine ⟨js', h_read_current, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using andi_run_vreg_xreg vd rs imm js x h_read_current hvd

/-- `ANDI` from a real source to a virtual destination, also exposing that one
chosen virtual register is preserved. -/
theorem exists_state_after_andi_run_vreg_xreg_preserving_value
    (vd vkeep : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x keep : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (h_keep : js.vregs vkeep = keep)
    (h_ne : vkeep ≠ vd)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = x &&& sign_extend (m := 64) imm ∧
      js'.vregs vkeep = keep ∧
      (execInstr (.ANDI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨js', h_read_current, h_sail_after_andi, h_write, h_preserves, h_run⟩ :=
    exists_state_after_andi_run_vreg_xreg_of_sail_eq vd rs imm js s x h_sail h_read hvd
  refine ⟨js', h_read_current, ?_, h_write, ?_, h_run⟩
  · rw [h_sail_after_andi, h_sail]
  · rw [h_preserves vkeep h_ne]
    exact h_keep

end JoltISA

end
