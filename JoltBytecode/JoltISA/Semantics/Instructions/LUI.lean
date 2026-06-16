import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# LUI instruction semantics

Run lemmas for the Jolt ISA `LUI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Jolt RV64 `LUI` writes the normalized immediate directly. -/
theorem execInstr_lui_vreg_run (vd : VReg) (imm : BitVec 64)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.LUI (.vreg vd) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then imm else js.vregs r } := by
  unfold execInstr writeDst
  exact writeVReg_retire_run_of_writable vd imm js hvd

end JoltISA

end
