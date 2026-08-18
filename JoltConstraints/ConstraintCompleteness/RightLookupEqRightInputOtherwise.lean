import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupEqRightInputOtherwise
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupEqRightInputOtherwise trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rightLookupEqRightInputOtherwise trace.metadata.toJoltPublicInputs witness

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
  have adviceFlag_from_trace :
      witness.opFlag .advice i =
        HonestWitness.fieldBool (HonestWitness.adviceOperands row.instruction) := by
    rfl
  have rightLookup_from_trace :
      witness.rightLookupOperand i =
        HonestWitness.fieldFromU128 (HonestWitness.lookupOperands row).2 := by
    rfl
  have rightInput_from_trace :
      witness.rightInstructionInput i =
        HonestWitness.fieldFromI128 (HonestWitness.instructionInputs row).2 := by
    rfl

  rw [addFlag_from_trace, subFlag_from_trace, mulFlag_from_trace,
    adviceFlag_from_trace, rightLookup_from_trace, rightInput_from_trace]
  rcases row with ⟨instruction, instructionRow, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp [HonestWitness.fieldBool, HonestWitness.addOperands,
      HonestWitness.subtractOperands, HonestWitness.multiplyOperands,
      HonestWitness.adviceOperands, HonestWitness.lookupOperands,
      HonestWitness.instructionInputs, HonestWitness.lookupSecondSource,
      HonestWitness.secondSource, HonestWitness.lowImmediate,
      HonestWitness.rightOperandIsImmediate,
      HonestWitness.signedInstructionImmediate]
  all_goals
    rw [fieldFromU64_low64_eq_fieldFromI128_of_lt]
    ring
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · first
      | rw [Int.toNat_lt' (by norm_num)]
        exact Int.emod_lt_of_pos _ (by norm_num)
      | exact Int.emod_lt_of_pos _ (by norm_num)
      | omega
      | exact BitVec.isLt _
      | norm_num [Xlen, InstructionLookupAddressBits]
    · first
      | rw [Int.toNat_lt' (by norm_num)]
        exact lt_trans (Int.emod_lt_of_pos _ (by norm_num)) (by norm_num)
      | exact lt_trans (Int.emod_lt_of_pos _ (by norm_num)) (by norm_num)
      | omega
      | exact lt_trans (BitVec.isLt _) (by
          norm_num [Xlen, InstructionLookupAddressBits])
      | norm_num [Xlen, InstructionLookupAddressBits]

end JoltConstraints.JoltConstraint.Completeness
