import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramFinalValueEqPublicIo
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramFinalValueEqPublicIo
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro address
  change
    (if trace.metadata.ramOutputMask address then (1 : F) else 0) *
        (HonestWitness.fieldFromU64 (F := F)
            (HonestWitness.memoryWord (HonestWitness.finalState trace)
              (trace.metadata.lowestMemoryAddress.toNat +
                8 * address.val)) -
          (trace.metadata.ramOutputValue address).toNat) = 0
  cases output_mask : trace.metadata.ramOutputMask address with
  | false => simp
  | true =>
      have output_eq :
          HonestWitness.memoryWord (HonestWitness.finalState trace)
              (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val) =
            trace.metadata.ramOutputValue address := by
        simpa [HonestWitness.finalState] using
          trace.ramOutputValid address output_mask
      rw [output_eq]
      simp [HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
