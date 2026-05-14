import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# VirtualShiftRightBitmask instruction semantics

Run lemmas for the Jolt ISA `VirtualShiftRightBitmask` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualShiftRightBitmask` from a real source to a virtual destination
materializes the bitmask consumed by `VirtualSRL` and `VirtualSRA`. -/
theorem execInstr_virtualShiftRightBitmask_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualShiftRightBitmask` can also read the shift amount from a virtual
register, which is how the word-shift expansions feed masked shift amounts
into `VirtualSRL`/`VirtualSRA`. -/
theorem execInstr_virtualShiftRightBitmask_vreg_vreg_run (vd vs : VReg)
    (js : SailJoltState) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value (js.vregs vs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
