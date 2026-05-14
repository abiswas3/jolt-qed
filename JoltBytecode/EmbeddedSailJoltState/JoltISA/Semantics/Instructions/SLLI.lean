import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# SLLI instruction semantics

Run lemmas for the Jolt ISA `SLLI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SLLI` on virtual registers is a pure virtual-register update. -/
theorem execInstr_slli_vreg_vreg_run (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    (execInstr (.SLLI (.vreg vd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left (js.vregs vs) shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLLI` from a real source to a virtual destination writes the shifted value
to the scratch register and leaves Sail unchanged. -/
theorem execInstr_slli_xreg_vreg_run (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.SLLI (.vreg vd) (.xreg rs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
