import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramReadEqRdWriteIfLoad
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramReadEqRdWriteIfLoad
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .ramReadEqRdWriteIfLoad witness
  unfold JoltConstraint.Satisfied
  intro i
  have loadFlag_from_trace :
      witness.opFlag .load i =
        HonestWitness.fieldBool (HonestWitness.isLoad (trace.rows i).instruction) := by
    rfl
  have ramRead_from_trace :
      witness.virtual .ramReadValue i =
        HonestWitness.fieldFromU64 (trace.rows i).ramReadValue := by
    rfl
  have rdWrite_from_trace :
      witness.rdWriteValue i =
        HonestWitness.fieldFromU64 (trace.rows i).rdWriteValue := by
    rfl
  rw [loadFlag_from_trace, ramRead_from_trace, rdWrite_from_trace]
  rcases hrow : trace.rows i with ⟨instruction, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp [HonestWitness.fieldBool, HonestWitness.isLoad,
      JoltTraceRow.ramReadValue, JoltTraceRow.rdWriteValue,
      CapturedState.ramReadValue, CapturedState.rdWriteValue]

end JoltConstraints.JoltConstraint.Completeness
