import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem lookupTableFlagsEqBytecodeReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .lookupTableFlagsEqBytecodeReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro table i
  change
    HonestWitness.fieldBool (F := F)
        (HonestWitness.lookupTable (trace.instrList i) == some table) -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => HonestWitness.fieldBool
          ((trace.metadata.toJoltPublicInputs.bytecode address).lookupTable ==
            some table)) i = 0
  rw [honest_bytecodeRead_eq_rowValue trace
    (fun row => HonestWitness.fieldBool (F := F)
      (row.lookupTable == some table)) i]
  have tableEq := HonestWitness.lookupTable_eq_bytecodeRow
    (trace.rows i) (trace.rowValid i).instructionKind_eq
  rw [show HonestWitness.lookupTable (trace.instrList i) =
        (trace.rows i).bytecodeRow.lookupTable by
      simpa [HonestTrace.instrList, ExecutionTrace.instrList] using tableEq]
  simp

end JoltConstraints.JoltConstraint.Completeness
