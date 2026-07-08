import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `BNE` equivalence statement. -/
def bneInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.BNE (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BNE).run js.sail)

theorem bneInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    bneInstrEqSailStatement imm rs2 rs1 js h := by
  sorry

end Natives

end
