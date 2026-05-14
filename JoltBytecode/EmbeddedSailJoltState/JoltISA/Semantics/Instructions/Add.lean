import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

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
theorem execInstr_add_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs + js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ADD` from two virtual sources to a real destination reads both virtual
sources, writes their sum through `wX_bits`, and preserves virtual registers. -/
theorem execInstr_add_vreg_vreg_xreg_run (rd : regidx) (lhs rhs : VReg)
    (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (js.vregs lhs + js.vregs rhs) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- `ADD` from two real sources to a real destination reads both architectural
sources and writes their sum through Sail. -/
theorem execInstr_add_xreg_xreg_xreg_run (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x + y) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `ADD` from two real sources to a real destination, with the output state
chosen by the instruction lemma. -/
theorem execInstr_add_xreg_xreg_xreg_run_of_reads (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail) :
    ∃ s',
      (execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (x + y) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x + y) js.sail
  exact ⟨s', execInstr_add_xreg_xreg_xreg_run rd rs1 rs2 js x y s' h₁ h₂ hw, hw⟩

end JoltISA

end
