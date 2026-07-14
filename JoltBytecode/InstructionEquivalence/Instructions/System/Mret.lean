import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- MRET equivalence statement.

Generated Sail's `execute_MRET` performs the trap-return postlude internally by
calling `exception_handler` for `CTL_MRET` and then `set_next_pc`. The current
assumption payload is intentionally `Unit`; the exact MRET assumptions will be
threaded once the proof is developed. -/
def mretProgramEqSailStatement
    (js : SailJoltState) (_h : Unit) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram JoltISA.mretProgram).run js) =
    (execute_MRET ()).run (systemProject js)

theorem mretProgram_eq_sail_projected
    (js : SailJoltState) (h : Unit) :
    mretProgramEqSailStatement js h := by
  sorry

end System

end
