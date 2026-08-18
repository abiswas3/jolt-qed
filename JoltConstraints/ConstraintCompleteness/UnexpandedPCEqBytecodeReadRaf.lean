import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem unexpandedPCEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .unexpandedPCEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  change
    HonestWitness.fieldFromU64 (F := F) (trace.rowMetadata i).unexpandedPC -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldFromU64
          (trace.metadata.toJoltPublicInputs.bytecode address).unexpandedPC) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldFromU64 (F := F) row.unexpandedPC) i]
  simp [HonestTrace.rowMetadata, ExecutionTrace.rowMetadata,
    JoltTraceRow.bytecodeRow]

end JoltConstraints.JoltConstraint.Completeness
