import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.JoltISA.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Sail operation descriptor for RV64 `MULHU`. -/
def sailMulhuOp : mul_op where
  result_part := VectorHalf.High
  signed_rs1 := Signedness.Unsigned
  signed_rs2 := Signedness.Unsigned

/-- Main native `MULHU` equivalence statement. -/
def mulhuInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.MULHU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_MUL rs2 rs1 rd sailMulhuOp).run js.sail)

theorem mulhuInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulhuInstrEqSailStatement rs2 rs1 rd js h := by
  sorry

end Natives

end
