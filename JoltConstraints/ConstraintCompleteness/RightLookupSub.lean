import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupSub
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupSub
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rightLookupSub witness

  unfold JoltConstraint.Satisfied
  intro i
  let instruction := trace.instrList i
  let metadata := trace.metadata.row i
  let before := trace.preState i
  let after := trace.postState i

  have subFlag_from_trace :
      witness.opFlag .subtractOperands i =
        HonestWitness.fieldBool (HonestWitness.subtractOperands instruction) := by
    rfl
  have rightLookup_from_trace :
      witness.rightLookupOperand i =
        HonestWitness.fieldFromU128
          (HonestWitness.lookupOperands instruction metadata before after).2 := by
    rfl
  have leftInput_from_trace :
      witness.leftInstructionInput i =
        HonestWitness.fieldFromU64
          (HonestWitness.instructionInputs instruction metadata before).1 := by
    rfl
  have rightInput_from_trace :
      witness.rightInstructionInput i =
        HonestWitness.fieldFromI128
          (HonestWitness.instructionInputs instruction metadata before).2 := by
    rfl

  rw [subFlag_from_trace, rightLookup_from_trace, leftInput_from_trace,
    rightInput_from_trace]
  cases instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.subtractOperands,
      HonestWitness.multiplyOperands, HonestWitness.addOperands,
      HonestWitness.adviceOperands, HonestWitness.lookupOperands,
      HonestWitness.instructionInputs, HonestWitness.lookupFirstSource,
      HonestWitness.lookupSecondSource, HonestWitness.firstSource,
      HonestWitness.secondSource]
  rw [fieldFromU128_subLookup]
  simp
  ring

end JoltConstraints.JoltConstraint.Completeness
