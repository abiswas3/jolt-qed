import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# ANDI instruction semantics

Run lemmas for the Jolt ISA `ANDI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ANDI` on virtual registers reads the virtual source, writes the masked
value to the virtual destination, and leaves the Sail state unchanged. -/
theorem execInstr_andi_vreg_vreg_run (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) :
    (execInstr (.ANDI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ANDI` from a real source to a virtual destination masks the source value
and leaves Sail unchanged. -/
theorem execInstr_andi_xreg_vreg_run (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ANDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
