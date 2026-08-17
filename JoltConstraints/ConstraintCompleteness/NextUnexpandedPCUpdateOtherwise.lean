import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCUpdateOtherwise
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCUpdateOtherwise
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs metadata consistency for ordinary, compressed, virtual,
  -- and no-op rows.
  sorry

end JoltConstraints.JoltConstraint.Completeness
