import JoltConstraints.ConstraintCompleteness.Ra

namespace JoltConstraints.JoltConstraint.Completeness

universe u

/-! Shared finite-table facts for Rust's fixed/public bytecode read-RAF. -/

/-- Reading a public bytecode table column with an honest committed address
selects the exact proof-facing row attached to the current trace cycle. -/
theorem honest_bytecodeRead_eq_rowValue
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (value : JoltBytecodeRow → F)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).bytecodeRead
        (fun address => value
          (trace.metadata.toJoltPublicInputs.bytecode address)) i =
      value (trace.rows i).bytecodeRow := by
  rw [honest_bytecodeRead_eq_selected]
  simpa [HonestTrace.rowMetadata, ExecutionTrace.rowMetadata] using
    congrArg value ((trace.rowValid i).bytecodeRow_eq
      (trace.rowValid i).pcBound)

/-- Rust's address-identity table reads back the compact bytecode index. -/
theorem honest_bytecodeRead_address
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).bytecodeRead
        (fun address => (address.val : F)) i =
      ((trace.rowMetadata i).pc : F) := by
  rw [honest_bytecodeRead_eq_selected]

end JoltConstraints.JoltConstraint.Completeness
