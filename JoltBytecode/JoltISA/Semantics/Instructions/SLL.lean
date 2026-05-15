import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# SLL instruction semantics

Run lemmas for the Jolt ISA `SLL` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SLL` on virtual registers shifts one virtual value by the low six bits of
another virtual value. -/
theorem execInstr_sll_vreg_vreg_vreg_run (vd value shamt : VReg)
    (js : SailJoltState) :
    (execInstr (.SLL (.vreg vd) (.vreg value) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              shift_bits_left (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shamt) 5 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLL` can read the value from a real register and the shift amount from a
virtual register before writing a virtual scratch register. -/
theorem execInstr_sll_xreg_vreg_vreg_run (vd : VReg) (rs : regidx) (shamt : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.SLL (.vreg vd) (.xreg rs) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              shift_bits_left x (Sail.BitVec.extractLsb (js.vregs shamt) 5 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
