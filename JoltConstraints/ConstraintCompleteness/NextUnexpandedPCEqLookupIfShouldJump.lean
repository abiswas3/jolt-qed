import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCEqLookupIfShouldJump
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCEqLookupIfShouldJump
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs adjacent-row metadata consistency for jump targets.
  sorry

end JoltConstraints.JoltConstraint.Completeness
