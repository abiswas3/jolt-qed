import JoltConstraints.ConstraintCompleteness.Helpers

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCEqPCPlusImmIfShouldBranch
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied
    .nextUnexpandedPCEqPCPlusImmIfShouldBranch witness
  unfold JoltConstraint.Satisfied
  intro i
  let current := trace.rows i
  have shouldBranch_from_trace :
      witness.virtual .shouldBranch i =
        HonestWitness.fieldBool current.shouldBranch := by
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
  have immediate_from_trace :
      witness.virtual .imm i =
        HonestWitness.fieldFromInt
          (HonestWitness.instructionImmediate current.instruction) := by
    rfl
  rw [shouldBranch_from_trace, nextPC_from_trace, pc_from_trace,
    immediate_from_trace]
  cases hnext : HonestWitness.nextTraceIndex i with
  | none =>
      have current_eq : current = JoltTraceRow.noOp := by
        simpa [current] using trace.finalRow i hnext
      simp [HonestWitness.nextMetadata, hnext, current_eq,
        JoltTraceRow.noOp, JoltTraceRow.shouldBranch,
        HonestWitness.isBranch, HonestWitness.fieldBool]
  | some j =>
      let next := trace.rows j
      have pair_valid : JoltTracePair.Valid current next := by
        simpa [current, next] using trace.pairValid i j hnext
      have nextMetadata_eq :
          HonestWitness.nextMetadata trace i = some next.metadata := by
        simp [HonestWitness.nextMetadata, hnext, next,
          HonestTrace.rowMetadata, ExecutionTrace.rowMetadata]
      rw [nextMetadata_eq]
      change HonestWitness.fieldBool current.shouldBranch *
        (HonestWitness.fieldFromU64 next.metadata.unexpandedPC -
          HonestWitness.fieldFromU64 current.metadata.unexpandedPC -
          HonestWitness.fieldFromInt
            (HonestWitness.instructionImmediate current.instruction)) = 0
      cases shouldBranch : current.shouldBranch
      · simp [HonestWitness.fieldBool]
      · have target_eq := pair_valid.branchTarget shouldBranch
        rw [fieldFromU64_eq_add_fieldFromInt
          next.metadata.unexpandedPC current.metadata.unexpandedPC
          (HonestWitness.instructionImmediate current.instruction) target_eq]
        simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
