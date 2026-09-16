import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionFlag::{extract_indexed, to_field}.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::walk_cycles;
-- crates/jolt-riscv/src/instructions/i/noop.rs (padding sets only IsNoop).
noncomputable def InstructionFlags [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : _root_.InstructionFlags → Fin p.traceLength → F :=
  fun flag t =>
    if inBounds : t.val < executionTrace.size then
      let row := executionTrace[t.val]
      if JoltMetadata.instructionFlag program.expandedBytecode[row.rowIndex].instruction flag then
        1
      else 0
    else
      match flag with
      | .IsNoop => 1
      | _ => 0

end HonestWitness
