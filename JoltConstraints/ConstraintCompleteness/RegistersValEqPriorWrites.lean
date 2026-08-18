import JoltConstraints.ConstraintCompleteness.RegisterState

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem registersValEqPriorWrites
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .registersValEqPriorWrites
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro address i
  change
    HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.registerAtAddress (trace.preState i) address) -
        HonestWitness.strictPrefixSum
          (fun j =>
            (honest_witness (F := F) trace).rdWa address j *
              (honest_witness (F := F) trace).rdInc j) i = 0
  have state := honest_register_state_at_cycle
    (F := F) trace address i.val (Nat.le_of_lt i.isLt)
  have state' :
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.registerAtAddress (trace.preState i) address) =
        HonestWitness.strictPrefixSum
          (fun j =>
            (honest_witness (F := F) trace).rdWa address j *
              (honest_witness (F := F) trace).rdInc j) i := by
    simpa [HonestWitness.strictPrefixSum, HonestTrace.preState,
      currentStateIndex] using state
  rw [state']
  ring

end JoltConstraints.JoltConstraint.Completeness
