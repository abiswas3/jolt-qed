import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ANDN` equivalence statement. -/
def andnInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_ZBB_RTYPE rs2 rs1 rd brop_zbb.ANDN).run js.sail)

theorem andnInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    andnInstrEqSailStatement rs2 rs1 rd js h := by
  sorry

end Natives

end
