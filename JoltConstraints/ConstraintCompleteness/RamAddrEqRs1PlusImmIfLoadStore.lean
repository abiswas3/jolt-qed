import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramAddrEqRs1PlusImmIfLoadStore
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramAddrEqRs1PlusImmIfLoadStore
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .ramAddrEqRs1PlusImmIfLoadStore witness
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have loadFlag_from_trace :
      witness.opFlag .load i =
        HonestWitness.fieldBool (HonestWitness.isLoad row.instruction) := by
    rfl
  have storeFlag_from_trace :
      witness.opFlag .store i =
        HonestWitness.fieldBool (HonestWitness.isStore row.instruction) := by
    rfl
  have ramAddress_from_trace :
      witness.virtual .ramAddress i =
        HonestWitness.fieldFromU64 row.ramAddress := by
    rfl
  have rs1_from_trace :
      witness.rs1Value i = HonestWitness.fieldFromU64 row.rs1Value := by
    rfl
  have immediate_from_trace :
      witness.virtual .imm i =
        HonestWitness.fieldFromInt
          (HonestWitness.instructionImmediate row.instruction) := by
    rfl
  rw [loadFlag_from_trace, storeFlag_from_trace, ramAddress_from_trace,
    rs1_from_trace, immediate_from_trace]
  cases hload : HonestWitness.isLoad row.instruction <;>
    cases hstore : HonestWitness.isStore row.instruction
  · simp [HonestWitness.fieldBool]
  all_goals
    have memory_row :
        (HonestWitness.isLoad (trace.rows i).instruction ||
          HonestWitness.isStore (trace.rows i).instruction) = true := by
      simp [row, hload, hstore]
    have address_eq :
        (row.ramAddress.toNat : Int) =
          (row.rs1Value.toNat : Int) +
            HonestWitness.instructionImmediate row.instruction := by
      simpa [row] using (trace.rowValid i).effectiveAddress memory_row
    rw [fieldFromU64_eq_add_fieldFromInt
      row.ramAddress row.rs1Value
      (HonestWitness.instructionImmediate row.instruction) address_eq]
    ring

end JoltConstraints.JoltConstraint.Completeness
