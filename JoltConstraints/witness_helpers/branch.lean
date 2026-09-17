import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltBytecode.JoltISA.semantic_helpers

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Review TODOs from the previous implementation, retained pending approval.
-- TODO: What the fuck is this theorem even proving?
-- TODO: Does this have to be a monad? Can it be a pure function and we can rid of this
-- monadic business? Discuss, we name it branchDecisionPure
-- TODO: Understand what is happening under the False.elim world
-- We might not need it at all.

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch::{extract, to_field}.
noncomputable def ShouldBranch [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < executionTrace.size then
      let row : JoltTraceRow program := executionTrace[t.val]
      let instruction := program.expandedBytecode[row.rowIndex].instruction
      match instruction with
      | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _
      | .BGE lhs rhs _ | .BLTU lhs rhs _ | .BGEU lhs rhs _ =>
          let rs1val := JoltISA.sourceValue lhs row.preState
          let rs2val := JoltISA.sourceValue rhs row.preState
          if JoltISA.branchDecisionPure instruction rs1val rs2val then 1 else 0
      | _ => 0
    else 0

end HonestWitness
