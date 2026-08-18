import JoltConstraints.ConstraintCompleteness.RdWriteEqLookupIfWriteLookupToRD

namespace JoltConstraints

universe u

/-!
This file preserves the original one-constraint experiment. New completeness
proofs live in `JoltConstraints/ConstraintCompleteness/`, one small file per
constraint.
-/

def and_constraint
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  JoltConstraint.Satisfied .rdWriteEqLookupIfWriteLookupToRD publicInputs witness

theorem and_completeness
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    and_constraint trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  exact JoltConstraint.Completeness.rdWriteEqLookupIfWriteLookupToRD trace

end JoltConstraints
