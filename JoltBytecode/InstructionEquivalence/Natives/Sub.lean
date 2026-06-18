import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Semantics.Instructions.Sub

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `SUB` equivalence statement. -/
def subInstrEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js)
    ((execute_RTYPE rs2 rs1 rd rop.SUB).run js.sail)

private theorem subInstr_project_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    projectResult
        ((JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
      (execute_RTYPE rs2 rs1 rd rop.SUB).run js.sail := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst execute_RTYPE
    liftSail projectResult project
  simp only [h.rs1_read, h.rs2_read, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run]
  cases hwrite : wX_bits rd (h.rs1_val - h.rs2_val) js.sail with
  | ok _ _ =>
      rfl
  | error _ _ =>
      rfl

/-- Native `SUB` agrees with Sail `execute_RTYPE ... SUB`. -/
theorem subInstr_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    subInstrEqSailStatement rs2 rs1 rd js h := by
  constructor
  · exact subInstr_project_eq_sail rs2 rs1 rd js h
  · intro result js' hrun
    exact JoltISA.execInstr_preserves_protected
      (instr := .SUB (.xreg rd) (.xreg rs1) (.xreg rs2))
      (js := js) (js' := js') (result := result)
      (by simp only [JoltISA.InstrWritesNoProtectedVReg,
          JoltISA.DstWritesNoProtectedVReg])
      hrun

end Natives

end
