import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rs2EqRamWriteIfStore
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rs2EqRamWriteIfStore
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: connect successful Sail stores to the RAM-access value recorded by
  -- the Jolt trace. Reconstructing it from post-state memory also needs the
  -- ordinary-memory (not MMIO) access assumptions.
  sorry

end JoltConstraints.JoltConstraint.Completeness
