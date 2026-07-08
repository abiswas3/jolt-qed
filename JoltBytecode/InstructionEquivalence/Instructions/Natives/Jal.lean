import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `JAL` equivalence statement. -/
def jalInstrEqSailStatement
    (imm : BitVec 21)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.JAL (.xreg rd) imm)).run js) =
    ((execute_JAL imm rd).run js.sail)

theorem jalInstr_eq_sail
    (imm : BitVec 21)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    jalInstrEqSailStatement imm rd js h := by
  sorry

end Natives

end
