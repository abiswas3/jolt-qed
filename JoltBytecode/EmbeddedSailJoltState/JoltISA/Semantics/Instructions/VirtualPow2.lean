import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# VirtualPow2 instruction semantics

Run lemmas for the Jolt ISA `VirtualPow2` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualPow2` from a real source to a virtual destination writes
`2 ^ rs[5:0]` to the scratch virtual register and leaves Sail unchanged. -/
theorem virtual_pow2_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualPow2 (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_virtual_pow2_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
