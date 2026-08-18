import JoltConstraints.ConstraintCompleteness.Memory

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramValEqInitialValuePlusPriorIncrements
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramValEqInitialValuePlusPriorIncrements
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro address i
  change
    HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) -
        ((honest_witness (F := F) trace).initialRamValue
            trace.metadata.toJoltPublicInputs address +
          HonestWitness.strictPrefixSum
            (fun j =>
              (honest_witness (F := F) trace).ramRa address j *
                (honest_witness (F := F) trace).ramInc j) i) = 0
  have state := honest_ram_state_at_cycle (F := F) trace address i.val
    (Nat.le_of_lt i.isLt)
  have state' :
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.memoryWord (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val)) =
        (honest_witness (F := F) trace).initialRamValue
            trace.metadata.toJoltPublicInputs address +
          HonestWitness.strictPrefixSum
            (fun j =>
              (honest_witness (F := F) trace).ramRa address j *
                (honest_witness (F := F) trace).ramInc j) i := by
    simpa [HonestWitness.strictPrefixSum, HonestTrace.preState,
      currentStateIndex] using state
  rw [state']
  ring

end JoltConstraints.JoltConstraint.Completeness
