import JoltConstraints.ConstraintCompleteness.Bytecode

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem pcEqBytecodeReadRafAddress
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .pcEqBytecodeReadRafAddress
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  change
    ((trace.rowMetadata i).pc : F) -
      (honest_witness (F := F) trace).bytecodeRead
        (fun address => (address.val : F)) i = 0
  rw [honest_bytecodeRead_address]
  simp

end JoltConstraints.JoltConstraint.Completeness
