import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas
import JoltBytecode.EmbeddedSailJoltState.RegisterOps

/-!
# VirtualSignExtendWord instruction semantics

Run lemmas for the Jolt ISA `VirtualSignExtendWord` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualSignExtendWord` from a real source to a real destination reads the
source and writes `sext(source[31:0])`. -/
theorem execInstr_sextw_xreg_xreg_run (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (hr : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail =
      .ok () s') :
    (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hr, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, hw]

/-- `VirtualSignExtendWord` from a real source to a real destination, with the
output state chosen by the instruction lemma. -/
theorem execInstr_sextw_xreg_xreg_run_of_read (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (hr : rX_bits rs js.sail = .ok x js.sail) :
    ∃ s',
      (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } ∧
      wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail =
        .ok () s' := by
  obtain ⟨s', hw⟩ :=
    wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail
  exact ⟨s', execInstr_sextw_xreg_xreg_run rd rs js x s' hr hw, hw⟩

/-- `VirtualSignExtendWord` from a real source to a virtual destination computes
the word-sign-extended scratch value used by word operations. -/
theorem execInstr_sextw_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
