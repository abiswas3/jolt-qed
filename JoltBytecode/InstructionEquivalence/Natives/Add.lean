import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Semantics.Instructions.Add

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ADD` equivalence statement. -/
def addInstrEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js)
    ((execute_RTYPE rs2 rs1 rd rop.ADD).run js.sail)

private theorem addInstr_project_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    projectResult
        ((JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
      (execute_RTYPE rs2 rs1 rd rop.ADD).run js.sail := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst execute_RTYPE
    liftSail projectResult project
  simp only [h.rs1_read, h.rs2_read, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run]
  cases hwrite : wX_bits rd (h.rs1_val + h.rs2_val) js.sail with
  | ok _ _ =>
      rfl
  | error _ _ =>
      rfl

/-- Native `ADD` agrees with Sail `execute_RTYPE ... ADD`. -/
theorem addInstr_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    addInstrEqSailStatement rs2 rs1 rd js h := by
  constructor
  · exact addInstr_project_eq_sail rs2 rs1 rd js h
  · intro result js' hrun
    exact JoltISA.execInstr_preserves_protected
      (instr := .ADD (.xreg rd) (.xreg rs1) (.xreg rs2))
      (js := js) (js' := js') (result := result)
      (by simp only [JoltISA.InstrWritesNoProtectedVReg,
          JoltISA.DstWritesNoProtectedVReg])
      hrun

end Natives

end
