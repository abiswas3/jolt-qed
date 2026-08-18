import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem immEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .immEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  change
    HonestWitness.fieldFromInt (F := F)
        (trace.rows i).instructionRow.operands.imm -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldFromInt
          (trace.metadata.toJoltPublicInputs.bytecode address).instruction.operands.imm) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldFromInt (F := F)
      row.instruction.operands.imm) i]
  simp [JoltTraceRow.bytecodeRow]

end JoltConstraints.JoltConstraint.Completeness
