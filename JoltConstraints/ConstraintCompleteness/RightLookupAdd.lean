import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupAdd
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupAdd
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  -- TODO: add the trace invariant that signed AUIPC/alignment sums are
  -- nonnegative. `fieldFromU128 (BitVec.ofInt 128 sum)` differs from the
  -- field image of `sum` when a negative sum wraps modulo `2^128`.
  sorry

end JoltConstraints.JoltConstraint.Completeness
