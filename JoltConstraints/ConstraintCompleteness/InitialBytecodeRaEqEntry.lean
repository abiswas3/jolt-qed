import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem initialBytecodeRaEqEntry
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .initialBytecodeRaEqEntry
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  let initial : Fin params.traceLength :=
    ⟨0, by simp [JoltWitnessParams.traceLength]⟩
  change
    (honest_witness (F := F) trace).bytecodeRaProduct
        trace.metadata.entryBytecodeIndex initial - 1 = 0
  rw [honest_bytecodeRaProduct_eq_oneHot]
  have initialPC : (trace.rowMetadata initial).pc =
      trace.metadata.entryBytecodeIndex.val := by
    simpa [initial, HonestTrace.rowMetadata, ExecutionTrace.rowMetadata] using
      trace.initialBytecodeIndex
  simp [HonestWitness.oneHot, HonestWitness.fieldBool, initialPC]

end JoltConstraints.JoltConstraint.Completeness
