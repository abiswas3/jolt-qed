import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `NoOp` equivalence statement. -/
def noopInstrEqSailStatement
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr .NoOp).run js) =
    ((pure RETIRE_SUCCESS : SailM ExecutionResult).run js.sail)

theorem noopInstr_eq_sail
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    noopInstrEqSailStatement js h := by
  sorry

end Natives

end
