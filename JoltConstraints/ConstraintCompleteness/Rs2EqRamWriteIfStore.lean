import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rs2EqRamWriteIfStore
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rs2EqRamWriteIfStore trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .rs2EqRamWriteIfStore trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  have storeFlag_from_trace :
      witness.opFlag .store i =
        HonestWitness.fieldBool (HonestWitness.isStore (trace.rows i).instruction) := by
    rfl
  have rs2_from_trace :
      witness.rs2Value i =
        HonestWitness.fieldFromU64 (trace.rows i).rs2Value := by
    rfl
  have ramWrite_from_trace :
      witness.virtual .ramWriteValue i =
        HonestWitness.fieldFromU64 (trace.rows i).ramWriteValue := by
    rfl
  rw [storeFlag_from_trace, rs2_from_trace, ramWrite_from_trace]
  rcases hrow : trace.rows i with
    ⟨instruction, instructionRow, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp [HonestWitness.fieldBool, HonestWitness.isStore,
      JoltTraceRow.rs2Value, JoltTraceRow.ramWriteValue,
      CapturedState.rs2Value, CapturedState.ramWriteValue]

end JoltConstraints.JoltConstraint.Completeness
