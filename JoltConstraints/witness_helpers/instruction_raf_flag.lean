import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionRafFlag::{extract, to_field}.
-- Rust: crates/jolt-riscv/src/flags.rs::InterleavedBitsMarker::is_interleaved_operands;
-- crates/jolt-riscv/src/instructions/i/noop.rs (padding has no operand-combination flags).
noncomputable def InstructionRafFlag [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < executionTrace.size then
      let row := executionTrace[t.val]
      if JoltMetadata.instructionRafFlag program.expandedBytecode[row.rowIndex].instruction then
        1
      else 0
    else 0

end HonestWitness
