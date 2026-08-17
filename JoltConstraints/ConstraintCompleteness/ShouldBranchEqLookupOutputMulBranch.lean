import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem shouldBranchEqLookupOutputMulBranch
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .shouldBranchEqLookupOutputMulBranch
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .shouldBranchEqLookupOutputMulBranch witness

  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  let output := HonestWitness.lookupOutput row

  have lookupOutput_from_trace :
      witness.lookupOutput i = HonestWitness.fieldFromU64 output := by
    rfl
  have branchFlag_from_trace :
      witness.instructionFlag .branch i =
        HonestWitness.fieldBool (HonestWitness.isBranch row.instruction) := by
    rfl
  have shouldBranch_from_trace :
      witness.virtual .shouldBranch i =
        HonestWitness.fieldBool
          (HonestWitness.isBranch row.instruction && output == 1) := by
    rfl

  rw [lookupOutput_from_trace, branchFlag_from_trace,
    shouldBranch_from_trace]
  cases hbranch : HonestWitness.isBranch row.instruction
  · simp [HonestWitness.fieldBool]
  · obtain ⟨value, output_eq⟩ :=
      lookupOutput_eq_boolU64_of_isBranch
        row hbranch
    change output = HonestWitness.boolU64 value at output_eq
    rw [output_eq]
    cases value <;>
      simp [HonestWitness.boolU64, HonestWitness.fieldBool,
        HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
