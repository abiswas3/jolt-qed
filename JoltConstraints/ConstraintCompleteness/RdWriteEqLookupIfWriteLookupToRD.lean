import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rdWriteEqLookupIfWriteLookupToRD
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rdWriteEqLookupIfWriteLookupToRD
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rdWriteEqLookupIfWriteLookupToRD witness

  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i

  have writeFlag_from_trace :
      witness.writeLookupOutputToRD i =
        HonestWitness.fieldBool
          (HonestWitness.writesLookupOutput row.instruction) := by
    rfl

  have rdWriteValue_from_trace :
      witness.rdWriteValue i =
        HonestWitness.fieldFromU64 row.rdWriteValue := by
    rfl

  have lookupOutput_from_trace :
      witness.lookupOutput i =
        HonestWitness.fieldFromU64 (HonestWitness.lookupOutput row) := by
    rfl

  rw [writeFlag_from_trace, rdWriteValue_from_trace, lookupOutput_from_trace]

  cases h : HonestWitness.writesLookupOutput row.instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.lookupOutput, h]

end JoltConstraints.JoltConstraint.Completeness
