import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `AUIPC` equivalence statement. -/
def auipcInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.AUIPC (.xreg rd) imm)).run js) =
    ((execute_UTYPE imm rd uop.AUIPC).run js.sail)

/-- Native `AUIPC` agrees with Sail `execute_UTYPE ... AUIPC`. -/
theorem auipcInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    auipcInstrEqSailStatement imm rd js h := by
  sorry

end Natives

end
