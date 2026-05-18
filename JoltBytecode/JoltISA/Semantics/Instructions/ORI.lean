import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# ORI instruction semantics

Run lemmas for the Jolt ISA `ORI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ORI` from a real source to a virtual destination sets the immediate bits
in the source value and leaves Sail unchanged. -/
theorem ori_run_vreg_xreg (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ORI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x ||| sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ORI` from a real source to a virtual destination, packaged as an
instruction step from a known unchanged Sail state. -/
theorem exists_state_after_ori_run_vreg_xreg_of_sail_eq
    (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = x ||| sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.ORI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then x ||| sign_extend (m := 64) imm else js.vregs r }
  refine ⟨js', h_read_current, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using ori_run_vreg_xreg vd rs imm js x h_read_current

/-- `ORI` from a real source to a virtual destination, also exposing that one
chosen virtual register is preserved. -/
theorem exists_state_after_ori_run_vreg_xreg_preserving_value
    (vd vkeep : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x keep : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (h_keep : js.vregs vkeep = keep)
    (h_ne : vkeep ≠ vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = x ||| sign_extend (m := 64) imm ∧
      js'.vregs vkeep = keep ∧
      (execInstr (.ORI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨js', h_read_current, h_sail_after_ori, h_write, h_preserves, h_run⟩ :=
    exists_state_after_ori_run_vreg_xreg_of_sail_eq vd rs imm js s x h_sail h_read
  refine ⟨js', h_read_current, ?_, h_write, ?_, h_run⟩
  · rw [h_sail_after_ori, h_sail]
  · rw [h_preserves vkeep h_ne]
    exact h_keep

end JoltISA

end
