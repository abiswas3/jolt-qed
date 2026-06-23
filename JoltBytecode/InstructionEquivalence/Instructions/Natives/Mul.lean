import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Sail operation descriptor for RV64 `MUL`. -/
def sailMulOp : mul_op where
  result_part := VectorHalf.Low
  signed_rs1 := Signedness.Signed
  signed_rs2 := Signedness.Signed

/-- Main native `MUL` equivalence statement. -/
def mulInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_MUL rs2 rs1 rd sailMulOp).run js.sail)

theorem mulInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulInstrEqSailStatement rs2 rs1 rd js h := by
  sorry

end Natives

end
