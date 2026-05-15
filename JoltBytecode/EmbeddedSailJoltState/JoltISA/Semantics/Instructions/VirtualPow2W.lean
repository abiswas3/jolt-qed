import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# VirtualPow2W instruction semantics

Run lemmas for the Jolt ISA `VirtualPow2W` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualPow2W` is the word-sized power-of-two helper.  It writes
`2 ^ rs[4:0]` to a virtual destination and leaves Sail unchanged. -/
theorem virtual_pow2w_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualPow2W (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_virtual_pow2w_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
