import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- Sail EBREAK followed by the generated trap postlude. -/
def sailEbreakTrapEntry : SailM ExecutionResult := do
  let result ← execute_EBREAK ()
  sailTrapPostlude result

/-- EBREAK equivalence statement.

The current assumption payload is intentionally `Unit`; the exact EBREAK
assumptions will be threaded once the proof is developed. -/
def ebreakProgramEqSailStatement
    (js : SailJoltState) (_h : Unit) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram JoltISA.ebreakProgram).run js) =
    sailEbreakTrapEntry.run (systemProject js)

theorem ebreakProgram_eq_sail_projected
    (js : SailJoltState) (h : Unit) :
    ebreakProgramEqSailStatement js h := by
  sorry

end System

end
