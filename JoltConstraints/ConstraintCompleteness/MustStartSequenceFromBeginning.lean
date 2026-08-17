import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem mustStartSequenceFromBeginning
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .mustStartSequenceFromBeginning
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs consistency between the current row's sequence metadata
  -- and the next row's `isFirstInSequence` marker.
  sorry

end JoltConstraints.JoltConstraint.Completeness
