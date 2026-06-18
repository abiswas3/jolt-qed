import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualAssertEQReal instruction semantics

Run lemmas for the Jolt ISA `VirtualAssertEQReal` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful `VirtualAssertEQReal` reads the real register and leaves state unchanged. -/
theorem virtual_assert_eq_real_run_ok (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (h : js.vregs lhs = value) :
    (execInstr (.VirtualAssertEQ (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h]
  rfl

/-- Failed `VirtualAssertEQReal` throws an assertion error. -/
theorem virtual_assert_eq_real_run_err (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (h : js.vregs lhs ≠ value) :
    (execInstr (.VirtualAssertEQ (.vreg lhs) (.xreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertEQ") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg h]
  rfl

end JoltISA

end
