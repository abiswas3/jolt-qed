import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem instructionFlagsEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .instructionFlagsEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro flag i
  change
    HonestWitness.fieldBool (F := F)
        (HonestWitness.instructionFlagValue flag (trace.instrList i)) -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldBool
          ((trace.metadata.toJoltPublicInputs.bytecode address).instructionFlagValue flag)) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldBool (F := F)
      (row.instructionFlagValue flag)) i]
  have flagEq := HonestWitness.instructionFlagValue_eq_bytecodeRow
    (trace.rows i) flag (trace.rowValid i).instructionKind_eq
  rw [show HonestWitness.instructionFlagValue flag (trace.instrList i) =
        (trace.rows i).bytecodeRow.instructionFlagValue flag by
      simpa [HonestTrace.instrList, ExecutionTrace.instrList] using flagEq]
  simp

end JoltConstraints.JoltConstraint.Completeness
