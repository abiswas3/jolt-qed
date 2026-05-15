import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# ADDI instruction semantics

Run lemmas for the Jolt ISA `ADDI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ADDI` from a real register to a virtual register reads the architectural
source and writes the immediate sum to the virtual destination. -/
theorem addi_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ADDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then x + sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ADDI` from a real source to a real destination reads the source through
Sail and writes the immediate sum through Sail. -/
theorem addi_run_xreg_xreg (rd rs1 : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x + sign_extend (m := 64) imm) js.sail = .ok () s') :
    (execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `ADDI` from a real source to a real destination, with the output state
chosen by the instruction lemma. -/
theorem exists_state_after_addi_run_xreg_xreg (rd rs1 : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs1 js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (x + sign_extend (m := 64) imm) js.sail = .ok () s' := by
  obtain ⟨s', hw⟩ := wX_shape rd (x + sign_extend (m := 64) imm) js.sail
  exact ⟨s', addi_run_xreg_xreg rd rs1 imm js x s' h hw, hw⟩

end JoltISA

end
