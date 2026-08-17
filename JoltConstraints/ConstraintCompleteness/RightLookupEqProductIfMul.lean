import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupEqProductIfMul
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupEqProductIfMul
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rightLookupEqProductIfMul witness

  unfold JoltConstraint.Satisfied
  intro i
  let instruction := trace.instrList i
  let metadata := trace.metadata.row i
  let before := trace.preState i
  let after := trace.postState i

  have mulFlag_from_trace :
      witness.opFlag .multiplyOperands i =
        HonestWitness.fieldBool (HonestWitness.multiplyOperands instruction) := by
    rfl
  have rightLookup_from_trace :
      witness.rightLookupOperand i =
        HonestWitness.fieldFromU128
          (HonestWitness.lookupOperands instruction metadata before after).2 := by
    rfl
  have product_from_trace :
      witness.virtual .product i =
        HonestWitness.fieldFromInt
          (HonestWitness.productValue instruction metadata before) := by
    rfl

  rw [mulFlag_from_trace, rightLookup_from_trace, product_from_trace]
  cases instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.multiplyOperands,
      HonestWitness.subtractOperands, HonestWitness.addOperands,
      HonestWitness.adviceOperands, HonestWitness.lookupOperands,
      HonestWitness.productValue, HonestWitness.instructionInputs,
      HonestWitness.lookupFirstSource, HonestWitness.lookupSecondSource,
      HonestWitness.firstSource, HonestWitness.secondSource,
      HonestWitness.lowImmediate, HonestWitness.rightOperandIsImmediate,
      HonestWitness.signedInstructionImmediate,
      HonestWitness.instructionImmediate, HonestWitness.fieldFromInt,
      HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
