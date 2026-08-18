import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextPCEqPCPlusOneIfInline
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextPCEqPCPlusOneIfInline trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .nextPCEqPCPlusOneIfInline trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let current := trace.rows i
  have virtualFlag_from_trace :
      witness.opFlag .virtualInstruction i =
        HonestWitness.fieldBool (HonestWitness.isVirtual current.metadata) := by
    rfl
  have lastFlag_from_trace :
      witness.opFlag .isLastInSequence i =
        HonestWitness.fieldBool
          (HonestWitness.isLastInSequence current.metadata) := by
    rfl
  have nextPC_from_trace :
      witness.virtual .nextPC i =
        match HonestWitness.nextMetadata trace i with
        | some metadata => (metadata.pc : F)
        | none => 0 := by
    rfl
  have pc_from_trace : witness.virtual .pc i = (current.metadata.pc : F) := by
    rfl
  rw [virtualFlag_from_trace, lastFlag_from_trace, nextPC_from_trace,
    pc_from_trace]
  cases hnext : HonestWitness.nextTraceIndex i with
  | none =>
      have current_eq : current = JoltTraceRow.noOp := by
        simpa [current] using trace.finalRow i hnext
      simp [HonestWitness.nextMetadata, hnext, current_eq,
        JoltTraceRow.noOp, HonestWitness.isVirtual,
        HonestWitness.isLastInSequence, HonestWitness.fieldBool]
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
        (HonestWitness.fieldBool (HonestWitness.isVirtual current.metadata) -
          HonestWitness.fieldBool
            (HonestWitness.isLastInSequence current.metadata)) *
        ((next.metadata.pc : F) - (current.metadata.pc : F) - 1) = 0
      cases remaining : current.metadata.virtualSequenceRemaining with
      | none =>
          simp [HonestWitness.isVirtual, HonestWitness.isLastInSequence,
            remaining, HonestWitness.fieldBool]
      | some n =>
          cases n with
          | zero =>
              simp [HonestWitness.isVirtual, HonestWitness.isLastInSequence,
                remaining, HonestWitness.fieldBool]
          | succ n =>
              have pc_eq : next.metadata.pc = current.metadata.pc + 1 :=
                pair_valid.inlinePC (by
                  simp [HonestWitness.isVirtual, remaining]) (by
                  simp [HonestWitness.isLastInSequence, remaining])
              have pc_eq_field :
                  (next.metadata.pc : F) =
                    (current.metadata.pc : F) + 1 := by
                rw [pc_eq, Nat.cast_add]
                norm_num
              rw [pc_eq_field]
              simp [HonestWitness.isVirtual, HonestWitness.isLastInSequence,
                remaining, HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
