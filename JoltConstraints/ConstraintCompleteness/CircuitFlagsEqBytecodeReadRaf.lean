import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem circuitFlagsEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .circuitFlagsEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro flag i
  change
    HonestWitness.fieldBool (F := F)
        (HonestWitness.circuitFlagValue flag
          (trace.instrList i) (trace.rowMetadata i)) -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldBool
          ((trace.metadata.toJoltPublicInputs.bytecode address).circuitFlagValue flag)) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldBool (F := F)
      (row.circuitFlagValue flag)) i]
  have flagEq := HonestWitness.circuitFlagValue_eq_bytecodeRow
    (trace.rows i) flag (trace.rowValid i).instructionKind_eq
  rw [show HonestWitness.circuitFlagValue flag
      (trace.instrList i) (trace.rowMetadata i) =
        (trace.rows i).bytecodeRow.circuitFlagValue flag by
      simpa [HonestTrace.instrList, ExecutionTrace.instrList,
        HonestTrace.rowMetadata, ExecutionTrace.rowMetadata] using flagEq]
  simp

end JoltConstraints.JoltConstraint.Completeness
