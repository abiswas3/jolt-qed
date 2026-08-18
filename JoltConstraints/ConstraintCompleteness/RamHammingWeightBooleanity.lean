import JoltConstraints.constraints

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramHammingWeightBooleanity
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramHammingWeightBooleanity
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  change
    HonestWitness.fieldBool (F := F)
          (match HonestWitness.ramAccessAddress (trace.rows i) with
          | some address => address != 0
          | none => false) *
        HonestWitness.fieldBool (F := F)
          (match HonestWitness.ramAccessAddress (trace.rows i) with
          | some address => address != 0
          | none => false) -
      HonestWitness.fieldBool (F := F)
        (match HonestWitness.ramAccessAddress (trace.rows i) with
        | some address => address != 0
        | none => false) = 0
  cases value : (match HonestWitness.ramAccessAddress (trace.rows i) with
    | some address => address != 0
    | none => false) <;>
    simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
