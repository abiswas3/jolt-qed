import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem leftLookupZeroUnlessAddSubMul
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .leftLookupZeroUnlessAddSubMul trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .leftLookupZeroUnlessAddSubMul trace.metadata.toJoltPublicInputs witness

  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i

  have addFlag_from_trace :
      witness.opFlag .addOperands i =
        HonestWitness.fieldBool (HonestWitness.addOperands row.instruction) := by
    rfl
  have subFlag_from_trace :
      witness.opFlag .subtractOperands i =
        HonestWitness.fieldBool (HonestWitness.subtractOperands row.instruction) := by
    rfl
  have mulFlag_from_trace :
      witness.opFlag .multiplyOperands i =
        HonestWitness.fieldBool (HonestWitness.multiplyOperands row.instruction) := by
    rfl
  have leftLookup_from_trace :
      witness.leftLookupOperand i =
        HonestWitness.fieldFromU64 (HonestWitness.lookupOperands row).1 := by
    rfl

  rw [addFlag_from_trace, subFlag_from_trace, mulFlag_from_trace,
    leftLookup_from_trace]
  rcases row with ⟨instruction, instructionRow, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp [HonestWitness.fieldBool, HonestWitness.addOperands,
      HonestWitness.subtractOperands, HonestWitness.multiplyOperands,
      HonestWitness.adviceOperands, HonestWitness.signedInstructionImmediate,
      HonestWitness.lookupOperands,
      HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
