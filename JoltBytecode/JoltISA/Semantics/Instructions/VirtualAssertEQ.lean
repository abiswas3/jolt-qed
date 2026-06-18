import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualAssertEQ instruction semantics

Run lemmas for the Jolt ISA `VirtualAssertEQ` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful `VirtualAssertEQ` leaves the full Jolt state unchanged. -/
theorem virtual_assert_eq_run_ok (lhs rhs : VReg) (js : SailJoltState)
    (h : js.vregs lhs = js.vregs rhs) :
    (execInstr (.VirtualAssertEQ (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h]
  rfl

/-- Failed `VirtualAssertEQ` throws an assertion error. -/
theorem virtual_assert_eq_run_err (lhs rhs : VReg) (js : SailJoltState)
    (h : js.vregs lhs ≠ js.vregs rhs) :
    (execInstr (.VirtualAssertEQ (.vreg lhs) (.vreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertEQ") js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg h]
  rfl

end JoltISA

end
