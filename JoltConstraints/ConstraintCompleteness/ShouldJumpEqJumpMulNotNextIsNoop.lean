import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem shouldJumpEqJumpMulNotNextIsNoop
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .shouldJumpEqJumpMulNotNextIsNoop trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .shouldJumpEqJumpMulNotNextIsNoop trace.metadata.toJoltPublicInputs witness

  unfold JoltConstraint.Satisfied
  intro i
  let jump := HonestWitness.isJump (trace.instrList i)
  let nextIsNoop := match HonestWitness.nextInstruction trace i with
    | some instruction => HonestWitness.isNoop instruction
    | none => true

  have jump_from_trace :
      witness.opFlag .jump i = HonestWitness.fieldBool jump := by
    rfl
  have nextIsNoop_from_trace :
      witness.virtual .nextIsNoop i = HonestWitness.fieldBool nextIsNoop := by
    rfl
  have shouldJump_from_trace :
      witness.virtual .shouldJump i =
        HonestWitness.fieldBool (jump && !nextIsNoop) := by
    cases hnext : HonestWitness.nextTraceIndex i with
    | none =>
        have current_is_noop : trace.rows i = JoltTraceRow.noOp :=
          trace.finalRow i hnext
        simp [witness, honest_witness, jump, nextIsNoop,
          HonestWitness.nextInstruction, hnext, current_is_noop,
          HonestTrace.instrList, ExecutionTrace.instrList,
          JoltTraceRow.noOp, HonestWitness.isJump]
    | some j =>
        simp [witness, honest_witness, jump, nextIsNoop,
          HonestWitness.nextInstruction, hnext]

  rw [jump_from_trace, nextIsNoop_from_trace, shouldJump_from_trace]
  cases jump <;> cases nextIsNoop <;> simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
