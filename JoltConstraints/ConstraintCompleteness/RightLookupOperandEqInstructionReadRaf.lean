import JoltConstraints.ConstraintCompleteness.ReadAddress

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightLookupOperandEqInstructionReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightLookupOperandEqInstructionReadRaf
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
    HonestWitness.fieldFromU128 (F := F)
          (HonestWitness.lookupOperands row).2 -
        ∑ address : InstructionLookupAddress,
          (honest_witness (F := F) trace).instructionRaProduct address i *
            (HonestWitness.fieldFromU64 (F := F) address.rightOperand +
              HonestWitness.fieldBool
                  (HonestWitness.instructionRafFlagValue row.instruction) *
                ((address.val : F) -
                  HonestWitness.fieldFromU64 (F := F)
                    address.rightOperand)) = 0
  rw [sum_instructionRaProduct_mul]
  have operand_contract := valid.lookupAddressOperands
  cases raf_eq : HonestWitness.instructionRafFlagValue row.instruction with
  | false =>
      simp [raf_eq] at operand_contract
      unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
      rw [operand_contract.2]
      simp [row, HonestWitness.fieldBool]
  | true =>
      simp [raf_eq] at operand_contract
      unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
      rw [operand_contract.2]
      simp [row, HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
