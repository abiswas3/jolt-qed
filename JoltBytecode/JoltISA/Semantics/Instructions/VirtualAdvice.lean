import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualAdvice instruction semantics

Run lemmas for the Jolt ISA `VirtualAdvice` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualAdvice` writes the supplied advice value into a virtual register. -/
theorem virtual_advice_run (vd : VReg) (advice : BitVec 64) (js : SailJoltState) :
    (execInstr (.VirtualAdvice vd advice)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then advice else js.vregs r } := by
  unfold execInstr writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

end JoltISA

end
