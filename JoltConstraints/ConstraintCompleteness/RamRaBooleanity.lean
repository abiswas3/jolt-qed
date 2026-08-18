import JoltConstraints.constraints

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramRaBooleanity
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramRaBooleanity
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro chunk address i
  unfold JoltWitness.ramCommittedRa
  simp only [honest_witness]
  cases h : HonestWitness.remappedRamAddress trace (trace.rows i) with
  | none =>
      simp
  | some ramAddress =>
      change
        HonestWitness.oneHot (F := F) address.val
              ((params.ramCommittedSelector chunk).chunk ramAddress).val *
            HonestWitness.oneHot (F := F) address.val
              ((params.ramCommittedSelector chunk).chunk ramAddress).val -
          HonestWitness.oneHot (F := F) address.val
            ((params.ramCommittedSelector chunk).chunk ramAddress).val = 0
      cases selected : address.val ==
          ((params.ramCommittedSelector chunk).chunk ramAddress).val <;>
        simp [HonestWitness.oneHot, HonestWitness.fieldBool, selected]

end JoltConstraints.JoltConstraint.Completeness
