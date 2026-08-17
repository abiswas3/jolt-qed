import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramAddrEqRs1PlusImmIfLoadStore
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramAddrEqRs1PlusImmIfLoadStore
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: relate wrapped `BitVec` address addition to field addition. This
  -- needs an address no-overflow invariant (or a field encoding theorem).
  sorry

end JoltConstraints.JoltConstraint.Completeness
