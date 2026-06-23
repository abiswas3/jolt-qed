import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `AND` equivalence statement. -/
def andInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.AND (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.AND).run js.sail)

theorem andInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    andInstrEqSailStatement rs2 rs1 rd js h := by
  sorry

end Natives

end
