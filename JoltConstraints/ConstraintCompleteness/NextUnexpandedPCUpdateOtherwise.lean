import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCUpdateOtherwise
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCUpdateOtherwise trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .nextUnexpandedPCUpdateOtherwise trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let current := trace.rows i
  have shouldBranch_from_trace :
      witness.virtual .shouldBranch i =
        HonestWitness.fieldBool current.shouldBranch := by
    rfl
  have jumpFlag_from_trace :
      witness.opFlag .jump i =
        HonestWitness.fieldBool (HonestWitness.isJump current.instruction) := by
    rfl
  have nextPC_from_trace :
      witness.virtual .nextUnexpandedPC i =
        match HonestWitness.nextMetadata trace i with
        | some metadata => HonestWitness.fieldFromU64 metadata.unexpandedPC
        | none => 0 := by
    rfl
  have pc_from_trace :
      witness.virtual .unexpandedPC i =
        HonestWitness.fieldFromU64 current.metadata.unexpandedPC := by
    rfl
  have doNotUpdate_from_trace :
      witness.opFlag .doNotUpdateUnexpandedPC i =
        HonestWitness.fieldBool
          (HonestWitness.doNotUpdateUnexpandedPC
            current.instruction current.metadata) := by
    rfl
  have compressed_from_trace :
      witness.opFlag .isCompressed i =
        HonestWitness.fieldBool current.metadata.isCompressed := by
    rfl
  rw [shouldBranch_from_trace, jumpFlag_from_trace, nextPC_from_trace,
    pc_from_trace, doNotUpdate_from_trace, compressed_from_trace]
  cases hnext : HonestWitness.nextTraceIndex i with
  | none =>
      have current_eq : current = JoltTraceRow.noOp := by
        simpa [current] using trace.finalRow i hnext
      simp [HonestWitness.nextMetadata, hnext, current_eq,
        JoltTraceRow.noOp, JoltTraceRow.shouldBranch,
        HonestWitness.isBranch, HonestWitness.isJump,
        HonestWitness.doNotUpdateUnexpandedPC, HonestWitness.isNoop,
        HonestWitness.fieldBool, HonestWitness.fieldFromU64]
  | some j =>
      let next := trace.rows j
      have pair_valid : JoltTracePair.Valid current next := by
        simpa [current, next] using trace.pairValid i j hnext
      have nextMetadata_eq :
          HonestWitness.nextMetadata trace i = some next.metadata := by
        simp [HonestWitness.nextMetadata, hnext, next,
          HonestTrace.rowMetadata, ExecutionTrace.rowMetadata]
      rw [nextMetadata_eq]
      change
        (1 - HonestWitness.fieldBool current.shouldBranch -
          HonestWitness.fieldBool
            (HonestWitness.isJump current.instruction)) *
        (HonestWitness.fieldFromU64 next.metadata.unexpandedPC -
          HonestWitness.fieldFromU64 current.metadata.unexpandedPC - 4 +
          4 * HonestWitness.fieldBool
            (HonestWitness.doNotUpdateUnexpandedPC
              current.instruction current.metadata) +
          2 * HonestWitness.fieldBool current.metadata.isCompressed) = 0
      cases shouldBranch : current.shouldBranch
      · cases isJump : HonestWitness.isJump current.instruction
        · have target_eq := pair_valid.ordinaryTarget shouldBranch isJump
          rw [fieldFromU64_eq_fieldFromInt
            next.metadata.unexpandedPC _ target_eq]
          cases hDoNot : HonestWitness.doNotUpdateUnexpandedPC
              current.instruction current.metadata <;>
            cases hCompressed : current.metadata.isCompressed <;>
            simp [HonestWitness.fieldBool, HonestWitness.fieldFromInt,
              HonestWitness.fieldFromU64]
          all_goals ring
        · simp [HonestWitness.fieldBool]
      · have isJump :
            HonestWitness.isJump current.instruction = false :=
          isJump_eq_false_of_shouldBranch_eq_true current shouldBranch
        simp [HonestWitness.fieldBool, isJump]

end JoltConstraints.JoltConstraint.Completeness
