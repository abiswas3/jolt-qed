import JoltBytecode.InstructionEquivalence.Semantics.Lemmas
import JoltBytecode.InstructionEquivalence.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.Semantics.StateLemmas

/-!
# SUB instruction semantics

Run lemmas for the Jolt ISA `SUB` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SUB` on virtual registers writes `lhs - rhs` to the virtual destination. -/
theorem sub_run_vreg_vreg_vreg (vd lhs rhs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.SUB (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs - js.vregs rhs
            else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `SUB` from a real source and virtual source writes into a virtual destination. -/
theorem sub_run_vreg_xreg_vreg (vd : VReg) (lhs : regidx) (rhs : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.SUB (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x - js.vregs rhs else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `SUB` from two real sources to a real destination reads both architectural
sources and writes their difference through Sail. -/
theorem sub_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x - y) js.sail = .ok () s') :
    (execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `SUB` from two real sources to a real destination, with the output Sail
state exposed as the architectural write performed by the instruction. -/
theorem exists_state_after_sub_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail) :
    ∃ js',
      rX_bits rs1 js.sail = .ok x js.sail ∧
      rX_bits rs2 js.sail = .ok y js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (x - y) ∧
      (execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x - y) js.sail
  have h_sail_after_sub :
      s' = stateAfterWrite js.sail rd (x - y) :=
    wX_bits_eq_stateAfterWrite rd (x - y) js.sail s' hw
  exact ⟨{ sail := s', vregs := js.vregs },
    h₁,
    h₂,
    h_sail_after_sub,
    sub_run_xreg_xreg_xreg rd rs1 rs2 js x y s' h₁ h₂ hw⟩

/-- Existential single-write post-state for `SUB` on virtual registers. -/
theorem sub_run_vreg_vreg_vreg_ex (vd vs1 vs2 : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.SUB (.vreg vd) (.vreg vs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 - js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (sub_run_vreg_vreg_vreg vd vs1 vs2 js hvd)

end JoltISA

end
