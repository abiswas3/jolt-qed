import JoltConstraints.constraints

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem bytecodeRaBooleanity
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .bytecodeRaBooleanity
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro chunk address i
  change
    HonestWitness.oneHot (F := F) address.val
          ((params.bytecodeCommittedSelector chunk).chunk
            (trace.rowMetadata i).pc).val *
        HonestWitness.oneHot (F := F) address.val
          ((params.bytecodeCommittedSelector chunk).chunk
            (trace.rowMetadata i).pc).val -
      HonestWitness.oneHot (F := F) address.val
        ((params.bytecodeCommittedSelector chunk).chunk
          (trace.rowMetadata i).pc).val = 0
  cases h : address.val ==
      ((params.bytecodeCommittedSelector chunk).chunk
        (trace.rowMetadata i).pc).val <;>
    simp [HonestWitness.oneHot, HonestWitness.fieldBool, h]

end JoltConstraints.JoltConstraint.Completeness
