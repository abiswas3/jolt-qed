import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextPCEqPCPlusOneIfInline
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextPCEqPCPlusOneIfInline
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs adjacent-row virtual-sequence metadata consistency.
  sorry

end JoltConstraints.JoltConstraint.Completeness
