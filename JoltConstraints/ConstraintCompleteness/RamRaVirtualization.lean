import JoltConstraints.ConstraintCompleteness.Ra

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramRaVirtualization
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramRaVirtualization
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro address i
  change
    (match HonestWitness.remappedRamAddress trace (trace.rows i) with
      | some ramAddress =>
          HonestWitness.oneHot (F := F) address.val ramAddress
      | none => 0) -
        (honest_witness (F := F) trace).ramCommittedRaProduct address i = 0
  rw [honest_ramCommittedRaProduct_eq_oneHot]
  cases HonestWitness.remappedRamAddress trace (trace.rows i) <;> ring

end JoltConstraints.JoltConstraint.Completeness
