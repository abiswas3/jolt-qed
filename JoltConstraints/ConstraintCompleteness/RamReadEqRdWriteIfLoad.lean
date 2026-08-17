import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramReadEqRdWriteIfLoad
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramReadEqRdWriteIfLoad
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: connect successful Sail loads to the RAM-access value recorded by
  -- the Jolt trace. The current extractor reconstructs `memoryWord` directly,
  -- which also needs the ordinary-memory (not MMIO) access assumptions.
  sorry

end JoltConstraints.JoltConstraint.Completeness
