import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- ECALL equivalence statement.

The Sail side is `execute_ECALL` followed by the generated trap postlude,
because raw `execute_ECALL` only returns a `Trap`. The current assumption
payload is intentionally `Unit`; the exact ECALL assumptions will be threaded
once the proof is developed. -/
def ecallProgramEqSailStatement
    (js : SailJoltState) (_h : Unit) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram JoltISA.ecallProgram).run js) =
    sailEcallTrapEntry.run (systemProject js)

theorem ecallProgram_eq_sail_projected
    (js : SailJoltState) (h : Unit) :
    ecallProgramEqSailStatement js h := by
  sorry

end System

end
