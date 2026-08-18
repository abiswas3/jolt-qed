import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rdWriteEqPCPlusConstIfWritePCToRD
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rdWriteEqPCPlusConstIfWritePCToRD trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rdWriteEqPCPlusConstIfWritePCToRD trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have jumpFlag_from_trace :
      witness.opFlag .jump i =
        HonestWitness.fieldBool (HonestWitness.isJump row.instruction) := by
    rfl
  have rdWrite_from_trace :
      witness.rdWriteValue i = HonestWitness.fieldFromU64 row.rdWriteValue := by
    rfl
  have pc_from_trace :
      witness.virtual .unexpandedPC i =
        HonestWitness.fieldFromU64 row.metadata.unexpandedPC := by
    rfl
  have compressed_from_trace :
      witness.opFlag .isCompressed i =
        HonestWitness.fieldBool row.metadata.isCompressed := by
    rfl
  rw [jumpFlag_from_trace, rdWrite_from_trace, pc_from_trace,
    compressed_from_trace]
  cases isJump : HonestWitness.isJump row.instruction
  · simp [HonestWitness.fieldBool]
  · have link_eq :
        (row.rdWriteValue.toNat : Int) =
          (row.metadata.unexpandedPC.toNat : Int) + 4 -
            (if row.metadata.isCompressed then 2 else 0) := by
      simpa [row] using (trace.rowValid i).jumpLink (by
        simpa [row] using isJump)
    rw [fieldFromU64_eq_fieldFromInt row.rdWriteValue _ link_eq]
    cases row.metadata.isCompressed <;>
      simp [HonestWitness.fieldBool, HonestWitness.fieldFromInt,
        HonestWitness.fieldFromU64]
    all_goals ring

end JoltConstraints.JoltConstraint.Completeness
