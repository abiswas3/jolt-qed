import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# MULH instruction semantics

Run lemmas for the Jolt ISA `MULH` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `MULH` on virtual registers writes the signed high half of the product. -/
theorem mulh_run_vreg_vreg_vreg (vd lhs rhs : VReg) (js : SailJoltState) :
    (execInstr (.MULH (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then mulhs (js.vregs lhs) (js.vregs rhs)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
