import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.JoltISA.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SD` equivalence statement. -/
def sdInstrEqSailStatement
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : StoreProgramEqSailAssumptions imm rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.SD (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_STORE imm rs2 rs1 8).run js.sail)

theorem sdInstr_eq_sail
    (imm : BitVec 12)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : StoreProgramEqSailAssumptions imm rs2 rs1 js) :
    sdInstrEqSailStatement imm rs2 rs1 js h := by
  sorry

end Natives

end
