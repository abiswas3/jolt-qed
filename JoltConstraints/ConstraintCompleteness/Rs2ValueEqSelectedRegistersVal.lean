import JoltConstraints.ConstraintCompleteness.Register

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rs2ValueEqSelectedRegistersVal
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rs2ValueEqSelectedRegistersVal
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have valid : JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
      (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  change
    HonestWitness.fieldFromU64 (F := F) row.rs2Value -
        ∑ address : RegisterAddress,
          HonestWitness.registerAddressIndicator
              row.instructionRow.operands.rs2 address *
            HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.registerAtAddress (trace.preState i) address) = 0
  rw [sum_registerAddressIndicator_mul]
  rw [valid.rs2Value_eq]
  cases row.instructionRow.operands.rs2 <;>
    simp [HonestWitness.registerAtOptionalAddress,
      HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
