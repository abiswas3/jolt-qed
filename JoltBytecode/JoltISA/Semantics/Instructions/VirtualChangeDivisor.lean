import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualChangeDivisor instruction semantics

Run lemmas for the Jolt ISA `VirtualChangeDivisor` instructions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualChangeDivisor` reads real dividend/divisor and writes the adjusted divisor. -/
theorem virtual_change_divisor_run (vd : VReg) (dividend divisor : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (hdividend : rX_bits dividend js.sail = .ok x js.sail)
    (hdivisor : rX_bits divisor js.sail = .ok y js.sail) :
    (execInstr (.VirtualChangeDivisor vd dividend divisor)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then change_divisor_value x y else js.vregs r } := by
  unfold execInstr readVReg liftSail writeVReg
  simp only [hdividend, hdivisor, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualChangeDivisorW` reads virtual dividend/divisor and writes the adjusted divisor. -/
theorem virtual_change_divisor_w_run (vd dividend divisor : VReg)
    (js : SailJoltState) :
    (execInstr (.VirtualChangeDivisorW vd dividend divisor)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then change_divisor_w_value (js.vregs dividend) (js.vregs divisor)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
