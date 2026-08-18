import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem productEqLeftInputMulRightInput
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .productEqLeftInputMulRightInput trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  simp [JoltWitness.leftInstructionInput, JoltWitness.rightInstructionInput,
    honest_witness, HonestWitness.productValue,
    HonestWitness.fieldFromU64, HonestWitness.fieldFromI128,
    HonestWitness.fieldFromInt]

end JoltConstraints.JoltConstraint.Completeness
