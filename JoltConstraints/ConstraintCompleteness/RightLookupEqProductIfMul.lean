import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupEqProductIfMul
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupEqProductIfMul trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rightLookupEqProductIfMul trace.metadata.toJoltPublicInputs witness

  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i

  have mulFlag_from_trace :
      witness.opFlag .multiplyOperands i =
        HonestWitness.fieldBool (HonestWitness.multiplyOperands row.instruction) := by
    rfl
  have rightLookup_from_trace :
      witness.rightLookupOperand i =
        HonestWitness.fieldFromU128 (HonestWitness.lookupOperands row).2 := by
    rfl
  have product_from_trace :
      witness.virtual .product i =
        HonestWitness.fieldFromInt (HonestWitness.productValue row) := by
    rfl
  have immediate_matches :
      HonestWitness.instructionImmediateMatches row := by
    exact (trace.rowValid i).instructionImmediate_eq

  rw [mulFlag_from_trace, rightLookup_from_trace, product_from_trace]
  rcases row with ⟨instruction, instructionRow, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp_all [HonestWitness.fieldBool, HonestWitness.multiplyOperands,
      HonestWitness.subtractOperands, HonestWitness.addOperands,
      HonestWitness.adviceOperands, HonestWitness.lookupOperands,
      HonestWitness.productValue, HonestWitness.instructionInputs,
      HonestWitness.lookupFirstSource, HonestWitness.lookupSecondSource,
      HonestWitness.firstSource, HonestWitness.secondSource,
      HonestWitness.lowImmediate, HonestWitness.rightOperandIsImmediate,
      HonestWitness.signedInstructionImmediate,
      HonestWitness.instructionImmediateMatches,
      HonestWitness.instructionImmediate, HonestWitness.fieldFromInt,
      HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
