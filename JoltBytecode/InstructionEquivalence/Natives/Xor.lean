import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.JoltISA.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `XOR` equivalence statement. -/
def xorInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.XOR (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.XOR).run js.sail)

theorem xorInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    xorInstrEqSailStatement rs2 rs1 rd js h := by
  sorry

end Natives

end
