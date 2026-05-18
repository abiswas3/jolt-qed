import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# SRAI instruction semantics

Run lemmas for the Jolt ISA `SRAI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SRAI` on virtual registers is a pure virtual-register update. -/
theorem srai_run_vreg_vreg (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    (execInstr (.SRAI (.vreg vd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith (js.vregs vs) shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SRAI` from a real register to a virtual register reads the real source and
writes the arithmetic shift to the virtual destination. -/
theorem srai_run_vreg_xreg (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.SRAI (.vreg vd) (.xreg rs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith x shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SRAI` from a virtual register to a real register performs the final
sign-extending extraction step for signed loads. -/
theorem execInstr_srai_vreg_xreg_run (rd : regidx) (vs : VReg)
    (shamt : BitVec 6) (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (shift_bits_right_arith (js.vregs vs) shamt) js.sail = .ok () s') :
    (execInstr (.SRAI (.xreg rd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

end JoltISA

end
