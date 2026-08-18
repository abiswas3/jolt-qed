import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem instructionRafFlagEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .instructionRafFlagEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  change
    HonestWitness.fieldBool (F := F)
        (HonestWitness.instructionRafFlagValue (trace.instrList i)) -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldBool
          (trace.metadata.toJoltPublicInputs.bytecode address).instructionRafFlagValue) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldBool (F := F)
      row.instructionRafFlagValue) i]
  have flagEq := HonestWitness.instructionRafFlagValue_eq_bytecodeRow
    (trace.rows i) (trace.rowValid i).instructionKind_eq
  rw [show HonestWitness.instructionRafFlagValue (trace.instrList i) =
        (trace.rows i).bytecodeRow.instructionRafFlagValue by
      simpa [HonestTrace.instrList, ExecutionTrace.instrList] using flagEq]
  simp

end JoltConstraints.JoltConstraint.Completeness
