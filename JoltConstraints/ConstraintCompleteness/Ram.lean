import JoltConstraints.ConstraintCompleteness.Encoding

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem sum_oneHot_mul
    {n : Nat} {F : Type u} [Field F]
    (expected : Fin n) (values : Fin n → F) :
    (∑ actual : Fin n,
        HonestWitness.oneHot actual.val expected.val * values actual) =
      values expected := by
  classical
  rw [Finset.sum_eq_single expected]
  · simp [HonestWitness.oneHot, HonestWitness.fieldBool]
  · intro actual _ actual_ne
    have values_ne : actual.val ≠ expected.val := by
      intro values_eq
      exact actual_ne (Fin.ext values_eq)
    simp [HonestWitness.oneHot, HonestWitness.fieldBool, values_ne]
  · simp

theorem fieldFromU64_add_signedDifference
    {F : Type u} [Field F]
    (before after : HonestWitness.U64) :
    HonestWitness.fieldFromU64 (F := F) after =
      HonestWitness.fieldFromU64 (F := F) before +
        HonestWitness.fieldFromI128 (F := F)
          (BitVec.ofInt InstructionLookupAddressBits
            ((after.toNat : Int) - before.toNat)) := by
  have before_lt := before.isLt
  have after_lt := after.isLt
  have lower_bound :
      -(2 : Int) ^ (InstructionLookupAddressBits - 1) ≤
        (after.toNat : Int) - before.toNat := by
    norm_num [Xlen, InstructionLookupAddressBits] at before_lt after_lt ⊢
    omega
  have upper_bound :
      (after.toNat : Int) - before.toNat <
        (2 : Int) ^ (InstructionLookupAddressBits - 1) := by
    norm_num [Xlen, InstructionLookupAddressBits] at before_lt after_lt ⊢
    omega
  have difference_toInt :
      (BitVec.ofInt InstructionLookupAddressBits
        ((after.toNat : Int) - before.toNat)).toInt =
          (after.toNat : Int) - before.toNat := by
    exact BitVec.toInt_ofInt_eq_self
      (by norm_num [InstructionLookupAddressBits]) lower_bound upper_bound
  unfold HonestWitness.fieldFromU64 HonestWitness.fieldFromI128
  rw [difference_toInt]
  push_cast
  ring

theorem fieldFromU64_ramWriteValue_eq_readValue_add_increment
    {F : Type u} [Field F] (row : JoltTraceRow) :
    HonestWitness.fieldFromU64 (F := F) row.ramWriteValue =
      HonestWitness.fieldFromU64 (F := F) row.ramReadValue +
        HonestWitness.fieldFromI128 (F := F)
          (HonestWitness.ramIncrement row) := by
  by_cases is_store : HonestWitness.isStore row.instruction = true
  · rw [HonestWitness.ramIncrement, if_pos is_store]
    exact fieldFromU64_add_signedDifference row.ramReadValue row.ramWriteValue
  · have write_eq_read : row.ramWriteValue = row.ramReadValue := by
      rcases row with ⟨instruction, instructionRow, metadata, captured⟩
      cases instruction <;> cases captured <;>
        simp_all [HonestWitness.isStore, JoltTraceRow.ramReadValue,
          JoltTraceRow.ramWriteValue, CapturedState.ramReadValue,
          CapturedState.ramWriteValue]
    rw [HonestWitness.ramIncrement, if_neg is_store, write_eq_read]
    simp [HonestWitness.fieldFromI128]

end JoltConstraints.JoltConstraint.Completeness
