import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem shouldJumpEqJumpMulNotNextIsNoop
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .shouldJumpEqJumpMulNotNextIsNoop
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .shouldJumpEqJumpMulNotNextIsNoop witness

  unfold JoltConstraint.Satisfied
  intro i
  let jump := HonestWitness.isJump (trace.instrList i)
  let nextIsNoop := match HonestWitness.nextInstruction trace i with
    | some instruction => HonestWitness.isNoop instruction
    | none => false

  have jump_from_trace :
      witness.opFlag .jump i = HonestWitness.fieldBool jump := by
    rfl
  have nextIsNoop_from_trace :
      witness.virtual .nextIsNoop i = HonestWitness.fieldBool nextIsNoop := by
    rfl
  have shouldJump_from_trace :
      witness.virtual .shouldJump i =
        HonestWitness.fieldBool (jump && !nextIsNoop) := by
    cases hnext : HonestWitness.nextInstruction trace i <;>
      simp [witness, honest_witness, jump, nextIsNoop, hnext]

  rw [jump_from_trace, nextIsNoop_from_trace, shouldJump_from_trace]
  cases jump <;> cases nextIsNoop <;> simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
