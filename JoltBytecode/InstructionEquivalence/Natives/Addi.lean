import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.JoltISA.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ADDI` equivalence statement. -/
def addiInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ITYPE imm rs1 rd iop.ADDI).run js.sail)

theorem addiInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiInstrEqSailStatement imm rs1 rd js h := by
  sorry

end Natives

end
