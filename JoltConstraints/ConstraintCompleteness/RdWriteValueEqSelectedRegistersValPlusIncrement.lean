import JoltConstraints.ConstraintCompleteness.Register

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rdWriteValueEqSelectedRegistersValPlusIncrement
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rdWriteValueEqSelectedRegistersValPlusIncrement
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
    HonestWitness.fieldFromU64 (F := F) row.rdWriteValue -
        ∑ address : RegisterAddress,
          HonestWitness.registerAddressIndicator
              row.instructionRow.operands.rd address *
            (HonestWitness.fieldFromU64 (F := F)
                (HonestWitness.registerAtAddress (trace.preState i) address) +
              HonestWitness.fieldFromI128 (F := F)
                (HonestWitness.rdIncrement row)) = 0
  rw [sum_registerAddressIndicator_mul]
  cases destination_eq : row.instructionRow.operands.rd with
  | none =>
      have write_zero : row.rdWriteValue = 0 := by
        rw [valid.rdWriteValue_eq, destination_eq]
        rfl
      simp [write_zero, HonestWitness.fieldFromU64]
  | some destination =>
      have pre_eq :
          row.rdPreValue = HonestWitness.registerAtAddress
            (trace.preState i) destination := by
        simpa [destination_eq, HonestWitness.registerAtOptionalAddress] using
          valid.rdPreValue_eq
      change
        HonestWitness.fieldFromU64 (F := F) row.rdWriteValue -
          (HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.registerAtAddress (trace.preState i) destination) +
            HonestWitness.fieldFromI128 (F := F)
              (HonestWitness.rdIncrement row)) = 0
      rw [← pre_eq]
      rw [HonestWitness.rdIncrement, destination_eq]
      rw [fieldFromU64_add_signedDifference row.rdPreValue row.rdWriteValue]
      ring

end JoltConstraints.JoltConstraint.Completeness
