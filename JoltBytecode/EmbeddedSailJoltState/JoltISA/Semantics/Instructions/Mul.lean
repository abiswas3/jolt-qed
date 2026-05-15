import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# MUL instruction semantics

Run lemmas for the Jolt ISA `MUL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `MUL` from a virtual source and a real source to a virtual destination reads
the real source through Sail, writes the low product to the virtual destination,
and leaves the Sail state unchanged when the real read is state-preserving. -/
theorem mul_run_vreg_vreg_xreg (vd lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail) :
    (execInstr (.MUL (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs * y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `MUL` from a real source and a virtual source to a real destination
consumes a scratch virtual register and writes the product through Sail. -/
theorem mul_run_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x * js.vregs vs2) js.sail = .ok () s') :
    (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `MUL` from a real source and a virtual source to a real destination, with
the output state chosen by the instruction lemma. -/
theorem exists_state_after_mul_run_xreg_xreg_vreg (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (x * js.vregs vs2) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x * js.vregs vs2) js.sail
  exact ⟨s', mul_run_xreg_xreg_vreg rd rs1 vs2 js x s' h hw, hw⟩

/-- `MUL` from two real sources to a real destination reads both architectural
sources and writes the low product through Sail. -/
theorem mul_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x * y) js.sail = .ok () s') :
    (execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `MUL` from two real sources to a real destination, with the output state
chosen by the instruction lemma. -/
theorem exists_state_after_mul_run_xreg_xreg_xreg (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail) :
    ∃ s',
      (execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (x * y) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x * y) js.sail
  exact ⟨s', mul_run_xreg_xreg_xreg rd rs1 rs2 js x y s' h₁ h₂ hw, hw⟩

end JoltISA

end
