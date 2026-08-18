import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rs2RaEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rs2RaEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro register i
  change
    HonestWitness.registerAddressIndicator (F := F)
        (trace.rows i).instructionRow.operands.rs2 register -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.registerAddressIndicator
          (trace.metadata.toJoltPublicInputs.bytecode address).instruction.operands.rs2
          register) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.registerAddressIndicator (F := F)
      row.instruction.operands.rs2 register) i]
  simp [JoltTraceRow.bytecodeRow]

end JoltConstraints.JoltConstraint.Completeness
