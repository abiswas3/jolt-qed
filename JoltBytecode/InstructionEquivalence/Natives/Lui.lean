import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Semantics.Instructions.LUI

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `LUI` equivalence statement. -/
def luiInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : Unit) : Prop :=
  ProgramMatchesSailWithProtectedFrame js
    ((JoltISA.execLUI imm rd).run js)
    ((execute_UTYPE imm rd uop.LUI).run js.sail)

private theorem projectResult_liftSail_bind_retire
    (m : SailM Unit)
    (js : SailJoltState) :
    projectResult (((liftSail m >>= fun _ =>
      pure RETIRE_SUCCESS : JoltMonad ExecutionResult)).run js) =
      ((m >>= fun _ => pure RETIRE_SUCCESS : SailM ExecutionResult).run
        js.sail) := by
  rw [← liftSail_pure RETIRE_SUCCESS]
  rw [← liftSail_bind]
  exact liftSail_project _ js

private theorem luiInstr_project_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState) :
    projectResult ((JoltISA.execLUI imm rd).run js) =
      (execute_UTYPE imm rd uop.LUI).run js.sail := by
  unfold JoltISA.execLUI JoltISA.luiValue JoltISA.execInstr JoltISA.writeDst
    execute_UTYPE liftSail projectResult project
  simp only [bind, pure]
  exact projectResult_liftSail_bind_retire
    (wX_bits rd (sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12))))
    js

/-- Native `LUI` writes the normalized immediate in both Jolt and Sail. -/
theorem luiInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : Unit) :
    luiInstrEqSailStatement imm rd js h := by
  constructor
  · exact luiInstr_project_eq_sail imm rd js
  · intro result js' hrun
    exact JoltISA.execInstr_preserves_protected
      (instr := .LUI (.xreg rd) (JoltISA.luiValue imm))
      (js := js) (js' := js') (result := result)
      (by simp only [JoltISA.InstrWritesNoProtectedVReg,
          JoltISA.DstWritesNoProtectedVReg])
      hrun

end Natives

end
