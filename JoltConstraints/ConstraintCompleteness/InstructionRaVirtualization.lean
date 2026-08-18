import JoltConstraints.ConstraintCompleteness.Ra

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem instructionRaVirtualization
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .instructionRaVirtualization
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro virtualChunk address i
  change
    HonestWitness.oneHot (F := F) address.val
          ((params.instructionVirtualSelector virtualChunk).chunk
            (HonestWitness.lookupIndex (trace.rows i)).toNat).val -
        (honest_witness (F := F) trace).instructionCommittedRaProduct
          virtualChunk address i = 0
  rw [honest_instructionCommittedRaProduct_eq_oneHot]
  ring

end JoltConstraints.JoltConstraint.Completeness
