import JoltConstraints.ConstraintCompleteness.Memory

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramValFinalEqInitialValuePlusAllIncrements
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramValFinalEqInitialValuePlusAllIncrements
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro address
  change
    HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (HonestWitness.finalState trace)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) -
        ((honest_witness (F := F) trace).initialRamValue
            trace.metadata.toJoltPublicInputs address +
          ∑ i : Fin params.traceLength,
            (honest_witness (F := F) trace).ramRa address i *
              (honest_witness (F := F) trace).ramInc i) = 0
  have state := honest_ram_state_at_cycle (F := F) trace address
    params.traceLength (le_refl params.traceLength)
  have state' :
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (HonestWitness.finalState trace)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
        (honest_witness (F := F) trace).initialRamValue
            trace.metadata.toJoltPublicInputs address +
          ∑ i : Fin params.traceLength,
            (honest_witness (F := F) trace).ramRa address i *
              (honest_witness (F := F) trace).ramInc i := by
    simpa [HonestWitness.finalState] using state
  rw [state']
  ring

end JoltConstraints.JoltConstraint.Completeness
