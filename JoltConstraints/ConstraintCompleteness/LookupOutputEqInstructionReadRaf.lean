import JoltConstraints.ConstraintCompleteness.ReadAddress

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem lookupOutputEqInstructionReadRaf
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .lookupOutputEqInstructionReadRaf
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have valid : JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
      (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  change
    HonestWitness.fieldFromU64 (F := F) (HonestWitness.lookupOutput row) -
        ∑ address : InstructionLookupAddress,
          (honest_witness (F := F) trace).instructionRaProduct address i *
            ∑ table : JoltLookupTable,
              HonestWitness.fieldFromU64 (F := F)
                  (JoltLookupTable.materializeEntry table address) *
                HonestWitness.fieldBool
                  (HonestWitness.lookupTable row.instruction == some table) = 0
  rw [sum_instructionRaProduct_mul]
  rw [sum_lookupTableFlag_mul]
  rw [lookupOutput_eq_selectedTable valid]
  cases table_eq :
      HonestWitness.lookupTable (trace.rows i).instruction <;>
    simp [row, HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
