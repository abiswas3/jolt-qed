import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltBytecode.JoltISA.semantic_helpers

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr propagates branch-operand read failures.
theorem branchDecision_error (instruction : JoltISA.Instr) (preState postState : SailJoltState)
    (error : Sail.Error exception)
    (branchDecisionFailed : JoltISA.branchDecision instruction preState = .error error postState) :
    JoltISA.execInstr instruction preState = .error error postState := by
  cases instruction <;>
    simp only [JoltISA.execInstr, bind, EStateM.bind, branchDecisionFailed]
  all_goals
    simp [JoltISA.branchDecision, pure, EStateM.pure] at branchDecisionFailed

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch::{extract, to_field}.
noncomputable def ShouldBranch [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < executionTrace.size then
      let row := executionTrace[t.val]
      match decision :
          JoltISA.branchDecision program.expandedBytecode[row.rowIndex].instruction row.preState with
      | .ok taken _ => if taken then 1 else 0
      -- TODO: Understand what is happening under the False.elim world
      | .error error state => False.elim (by
          have execInstrFailed := branchDecision_error _ _ state error decision
          rw [row.executes] at execInstrFailed
          cases execInstrFailed)
    else 0

end HonestWitness
