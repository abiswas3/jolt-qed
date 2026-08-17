import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rdWriteEqPCPlusConstIfWritePCToRD
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rdWriteEqPCPlusConstIfWritePCToRD
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: this needs metadata consistency: `unexpandedPC` and
  -- `isCompressed` must describe the executed jump row.
  sorry

end JoltConstraints.JoltConstraint.Completeness
