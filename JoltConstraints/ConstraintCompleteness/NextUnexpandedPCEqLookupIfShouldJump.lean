import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextUnexpandedPCEqLookupIfShouldJump
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextUnexpandedPCEqLookupIfShouldJump trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .nextUnexpandedPCEqLookupIfShouldJump trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let current := trace.rows i
  have shouldJump_from_trace :
      witness.virtual .shouldJump i =
        HonestWitness.fieldBool
          (HonestWitness.isJump current.instruction &&
            match HonestWitness.nextInstruction trace i with
            | some instruction => !(HonestWitness.isNoop instruction)
            | none => true) := by
    rfl
  have nextPC_from_trace :
      witness.virtual .nextUnexpandedPC i =
        match HonestWitness.nextMetadata trace i with
        | some metadata => HonestWitness.fieldFromU64 metadata.unexpandedPC
        | none => 0 := by
    rfl
  have lookupOutput_from_trace :
      witness.lookupOutput i =
        HonestWitness.fieldFromU64 (HonestWitness.lookupOutput current) := by
    rfl
  rw [shouldJump_from_trace, nextPC_from_trace, lookupOutput_from_trace]
  cases hnext : HonestWitness.nextTraceIndex i with
  | none =>
      have current_eq : current = JoltTraceRow.noOp := by
        simpa [current] using trace.finalRow i hnext
      simp [HonestWitness.nextInstruction, HonestWitness.nextMetadata, hnext,
        current_eq, JoltTraceRow.noOp, HonestWitness.isJump,
        HonestWitness.fieldBool]
  | some j =>
      let next := trace.rows j
      have pair_valid : JoltTracePair.Valid current next := by
        simpa [current, next] using trace.pairValid i j hnext
      have nextInstruction_eq :
          HonestWitness.nextInstruction trace i = some next.instruction := by
        simp [HonestWitness.nextInstruction, hnext, next,
          HonestTrace.instrList, ExecutionTrace.instrList]
      have nextMetadata_eq :
          HonestWitness.nextMetadata trace i = some next.metadata := by
        simp [HonestWitness.nextMetadata, hnext, next,
          HonestTrace.rowMetadata, ExecutionTrace.rowMetadata]
      rw [nextInstruction_eq, nextMetadata_eq]
      change HonestWitness.fieldBool (JoltTracePair.shouldJump current next) *
        (HonestWitness.fieldFromU64 next.metadata.unexpandedPC -
          HonestWitness.fieldFromU64 (HonestWitness.lookupOutput current)) = 0
      cases shouldJump : JoltTracePair.shouldJump current next
      · simp [HonestWitness.fieldBool]
      · have target_eq :
            next.metadata.unexpandedPC =
              HonestWitness.lookupOutput current :=
          pair_valid.jumpTarget shouldJump
        rw [target_eq]
        simp

end JoltConstraints.JoltConstraint.Completeness
