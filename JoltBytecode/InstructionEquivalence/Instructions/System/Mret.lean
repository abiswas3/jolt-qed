import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- MRET equivalence statement.

Generated Sail's `execute_MRET` performs the trap-return postlude internally by
calling `exception_handler` for `CTL_MRET` and then `set_next_pc`. -/
def mretProgramEqSailStatement
    (js : SailJoltState) (_h : MretProgramEqSailAssumptions js) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram JoltISA.mretProgram).run js) =
    (execute_MRET ()).run (systemProject js)

theorem mretProgram_eq_sail_projected
    (js : SailJoltState) (h : MretProgramEqSailAssumptions js) :
    mretProgramEqSailStatement js h := by
  sorry
  


end System

end
