import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCEqPCPlusImmIfShouldBranch
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs adjacent-row metadata consistency for taken branches,
  -- plus the corresponding field/bit-vector addition fact.
  sorry

end JoltConstraints.JoltConstraint.Completeness
