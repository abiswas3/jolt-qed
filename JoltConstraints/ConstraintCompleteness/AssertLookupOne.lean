import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem assertLookupOne
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .assertLookupOne
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .assertLookupOne witness
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have assertFlag_from_trace :
      witness.opFlag .assert i =
        HonestWitness.fieldBool (HonestWitness.isAssert row.instruction) := by
    rfl
  have lookupOutput_from_trace :
      witness.lookupOutput i =
        HonestWitness.fieldFromU64 (HonestWitness.lookupOutput row) := by
    rfl
  rw [assertFlag_from_trace, lookupOutput_from_trace]
  cases isAssert : HonestWitness.isAssert row.instruction
  · simp [HonestWitness.fieldBool]
  · have output_eq : HonestWitness.lookupOutput row = 1 := by
      simpa [row] using (trace.rowValid i).assertionAccepted (by
        simpa [row] using isAssert)
    rw [output_eq]
    simp [HonestWitness.fieldBool, HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
