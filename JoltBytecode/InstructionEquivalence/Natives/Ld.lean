import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.JoltISA.Semantics.Instructions

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `LD` equivalence statement. -/
def ldInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.LD (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_LOAD imm rs1 rd false 8).run js.sail)

theorem ldInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    ldInstrEqSailStatement imm rs1 rd js h := by
  sorry

end Natives

end
