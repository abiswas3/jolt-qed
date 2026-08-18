import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupAdd
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupAdd trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rightLookupAdd trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have addFlag_from_trace :
      witness.opFlag .addOperands i =
        HonestWitness.fieldBool (HonestWitness.addOperands row.instruction) := by
    rfl
  have rightLookup_from_trace :
      witness.rightLookupOperand i =
        HonestWitness.fieldFromU128 (HonestWitness.lookupOperands row).2 := by
    rfl
  have leftInput_from_trace :
      witness.leftInstructionInput i =
        HonestWitness.fieldFromU64 (HonestWitness.instructionInputs row).1 := by
    rfl
  have rightInput_from_trace :
      witness.rightInstructionInput i =
        HonestWitness.fieldFromI128 (HonestWitness.instructionInputs row).2 := by
    rfl
  have add_nonnegative :
      HonestWitness.addOperands row.instruction = true →
        0 ≤ ((HonestWitness.instructionInputs row).1.toNat : Int) +
          (HonestWitness.instructionInputs row).2.toInt := by
    simpa [row] using (trace.rowValid i).addInput_nonnegative
  rw [addFlag_from_trace, rightLookup_from_trace, leftInput_from_trace,
    rightInput_from_trace]
  cases isAdd : HonestWitness.addOperands row.instruction
  · simp [HonestWitness.fieldBool]
  · rw [fieldFrom_addLookup row isAdd (add_nonnegative isAdd)]
    simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
