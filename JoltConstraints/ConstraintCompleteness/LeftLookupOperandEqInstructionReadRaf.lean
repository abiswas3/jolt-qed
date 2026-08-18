import JoltConstraints.ConstraintCompleteness.ReadAddress

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem leftLookupOperandEqInstructionReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .leftLookupOperandEqInstructionReadRaf
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
    HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.lookupOperands row).1 -
        ∑ address : InstructionLookupAddress,
          (honest_witness (F := F) trace).instructionRaProduct address i *
            (HonestWitness.fieldFromU64 (F := F) address.leftOperand *
              (1 - HonestWitness.fieldBool
                (HonestWitness.instructionRafFlagValue row.instruction))) = 0
  rw [sum_instructionRaProduct_mul]
  have operand_contract := valid.lookupAddressOperands
  cases raf_eq : HonestWitness.instructionRafFlagValue row.instruction with
  | false =>
      simp [raf_eq] at operand_contract
      rw [operand_contract.1]
      simp [row, HonestWitness.fieldBool]
  | true =>
      simp [raf_eq] at operand_contract
      rw [operand_contract.1]
      simp [HonestWitness.fieldBool,
        HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
