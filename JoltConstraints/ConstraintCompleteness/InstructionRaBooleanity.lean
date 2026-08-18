import JoltConstraints.constraints

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem instructionRaBooleanity
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .instructionRaBooleanity
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro chunk address i
  change
    HonestWitness.oneHot (F := F) address.val
          ((params.instructionCommittedSelector chunk).chunk
            (HonestWitness.lookupIndex (trace.rows i)).toNat).val *
        HonestWitness.oneHot (F := F) address.val
          ((params.instructionCommittedSelector chunk).chunk
            (HonestWitness.lookupIndex (trace.rows i)).toNat).val -
      HonestWitness.oneHot (F := F) address.val
        ((params.instructionCommittedSelector chunk).chunk
          (HonestWitness.lookupIndex (trace.rows i)).toNat).val = 0
  cases h : address.val ==
      ((params.instructionCommittedSelector chunk).chunk
        (HonestWitness.lookupIndex (trace.rows i)).toNat).val <;>
    simp [HonestWitness.oneHot, HonestWitness.fieldBool, h]

end JoltConstraints.JoltConstraint.Completeness
