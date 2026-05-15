import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# XOR instruction semantics

Run lemmas for the Jolt ISA `XOR` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `XOR` from a real source and a virtual source to a virtual destination reads
the real source through Sail and writes the xor result. -/
theorem xor_run_vreg_xreg_vreg (vd : VReg) (lhs : regidx) (rhs : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail) :
    (execInstr (.XOR (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x ^^^ js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `XOR` from a real source and a virtual source to a virtual destination,
packaged from a known virtual-source value and a known base Sail state. -/
theorem exists_state_after_xor_run_vreg_xreg_vreg
    (vd : VReg) (lhs : regidx) (rhs : VReg) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : rX_bits lhs s = .ok x s)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      rX_bits lhs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = x ^^^ y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.XOR (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_lhs_current : rX_bits lhs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_lhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then x ^^^ js.vregs rhs else js.vregs r }
  refine ⟨js', h_lhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js', h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using xor_run_vreg_xreg_vreg vd lhs rhs js x h_lhs_current

/-- `XOR` on virtual sources and a virtual destination reads both virtual
sources, writes their xor, and leaves the Sail state unchanged. -/
theorem xor_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs ^^^ js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `XOR` from two virtual sources to a virtual destination, packaged from
known virtual-source values. -/
theorem exists_state_after_xor_run_vreg_vreg_vreg
    (vd lhs rhs : VReg) (js : SailJoltState) (x y : BitVec 64)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x ^^^ y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs lhs ^^^ js.vregs rhs else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_lhs, h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using xor_run_vreg_vreg_vreg vd lhs rhs js

end JoltISA

end
