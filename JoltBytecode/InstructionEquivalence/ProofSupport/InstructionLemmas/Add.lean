import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# ADD instruction semantics

Run lemmas for the Jolt ISA `ADD` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ADD` on virtual sources and a virtual destination reads both virtual
sources, writes their sum, and leaves the Sail state unchanged. -/
theorem add_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs + js.vregs rhs else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `ADD` from two virtual sources to a virtual destination, packaged as an
instruction step from known virtual-source values. -/
theorem exists_state_after_add_run_vreg_vreg_vreg
    (vd lhs rhs : VReg) (js : SailJoltState) (x y : BitVec 64)
    (hvd : WritableVReg vd)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x + y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs lhs + js.vregs rhs else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_lhs, h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using add_run_vreg_vreg_vreg vd lhs rhs js hvd

/-- `ADD` from two virtual sources to a real destination reads both virtual
sources, writes their sum through `wX_bits`, and preserves virtual registers. -/
theorem add_run_xreg_vreg_vreg (rd : regidx) (lhs rhs : VReg)
    (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (js.vregs lhs + js.vregs rhs) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- `ADD` from two virtual sources to a real destination, packaged from known
virtual-source values and a known base Sail state. -/
theorem exists_state_after_add_run_xreg_vreg_vreg
    (rd : regidx) (lhs rhs : VReg) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      js'.sail = stateAfterWrite s rd (x + y) ∧
      (execInstr (.ADD (.xreg rd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', h_write⟩ := wX_shape rd (x + y) s
  have h_write_current :
      wX_bits rd (js.vregs lhs + js.vregs rhs) js.sail = .ok () s' := by
    simpa only [h_sail, h_lhs, h_rhs] using h_write
  have h_sail_after_add :
      s' = stateAfterWrite s rd (x + y) :=
    wX_bits_eq_stateAfterWrite rd (x + y) s s' h_write
  exact ⟨{ sail := s', vregs := js.vregs },
    h_sail_after_add,
    add_run_xreg_vreg_vreg rd lhs rhs js s' h_write_current⟩

/-- `ADD` from two real sources to a real destination reads both architectural
sources and writes their sum through Sail. -/
theorem add_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x + y) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `ADD` from two real sources to a real destination, with the output Sail
state exposed as the architectural write performed by the instruction. -/
theorem exists_state_after_add_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      rX_bits rs2 js.sail = .ok y js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (x + y) ∧
      (execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x + y) js.sail
  have h_sail_after_add :
      s' = stateAfterWrite js.sail rd (x + y) :=
    wX_bits_eq_stateAfterWrite rd (x + y) js.sail s' hw
  exact ⟨{ sail := s', vregs := js.vregs },
    h₁,
    h₂,
    h_sail_after_add,
    add_run_xreg_xreg_xreg rd rs1 rs2 js x y s' h₁ h₂ hw⟩

/-- Existential single-write post-state for `ADD` on virtual registers. -/
theorem add_run_vreg_vreg_vreg_ex (vd vs1 vs2 : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.ADD (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 + js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (add_run_vreg_vreg_vreg vd vs1 vs2 js hvd)

end JoltISA

end
