import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::OpFlag::{extract_indexed, to_field}.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::walk_cycles;
-- crates/jolt-riscv/src/instructions/i/noop.rs (padding has no circuit flags).
noncomputable def OpFlags [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : CircuitFlags → Fin p.traceLength → F :=
  fun flag t =>
    if inBounds : t.val < executionTrace.size then
      let row := executionTrace[t.val]
      if JoltMetadata.circuitFlag program.expandedBytecode[row.rowIndex] flag then 1 else 0
    else 0

end HonestWitness
