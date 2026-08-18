import JoltConstraints.ConstraintCompleteness.Ra

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem instructionVirtualSelectors_jointly_injective
    {params : JoltWitnessParams} (valid : params.Valid)
    {left right : InstructionLookupAddress}
    (chunks_eq : ∀ chunk : Fin params.instructionVirtualRaCount,
      (params.instructionVirtualSelector chunk).chunk left.val =
        (params.instructionVirtualSelector chunk).chunk right.val) :
    left = right := by
  apply Fin.ext
  apply raChunkSelectors_jointly_injective
    valid.lookupVirtualChunkBitsPositive
  · rw [valid.instructionVirtualChunksTile]
    exact left.isLt
  · rw [valid.instructionVirtualChunksTile]
    exact right.isLt
  · simpa [JoltWitnessParams.instructionVirtualSelector] using chunks_eq

theorem honest_instructionRaProduct_eq_oneHot
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (address : InstructionLookupAddress)
    (i : Fin params.traceLength) :
    (honest_witness (F := F) trace).instructionRaProduct address i =
      HonestWitness.oneHot (F := F) address.val
        (HonestWitness.lookupIndex (trace.rows i)).toNat := by
  let selected : InstructionLookupAddress :=
    InstructionLookupAddress.ofBits
      (HonestWitness.lookupIndex (trace.rows i))
  have selected_val :
      selected.val = (HonestWitness.lookupIndex (trace.rows i)).toNat := by
    rfl
  change
    (∏ chunk : Fin params.instructionVirtualRaCount,
      HonestWitness.oneHot (F := F)
        ((params.instructionVirtualSelector chunk).chunk address.val).val
        ((params.instructionVirtualSelector chunk).chunk
          (HonestWitness.lookupIndex (trace.rows i)).toNat).val) =
      HonestWitness.oneHot (F := F) address.val
        (HonestWitness.lookupIndex (trace.rows i)).toNat
  rw [← selected_val]
  by_cases address_eq : address = selected
  · subst address
    simp [HonestWitness.oneHot, HonestWitness.fieldBool]
  · have differing_chunk :
        ∃ chunk : Fin params.instructionVirtualRaCount,
          (params.instructionVirtualSelector chunk).chunk address.val ≠
            (params.instructionVirtualSelector chunk).chunk selected.val := by
      by_contra no_differing_chunk
      push_neg at no_differing_chunk
      exact address_eq <|
        instructionVirtualSelectors_jointly_injective
          trace.metadataValid.paramsValid no_differing_chunk
    rcases differing_chunk with ⟨chunk, chunk_ne⟩
    have chunk_values_ne :
        ((params.instructionVirtualSelector chunk).chunk address.val).val ≠
          ((params.instructionVirtualSelector chunk).chunk selected.val).val := by
      intro values_eq
      exact chunk_ne (Fin.ext values_eq)
    have address_values_ne : address.val ≠ selected.val := by
      intro values_eq
      exact address_eq (Fin.ext values_eq)
    rw [Finset.prod_eq_zero (Finset.mem_univ chunk)]
    · simp [HonestWitness.oneHot, HonestWitness.fieldBool,
        address_values_ne]
    · simp [HonestWitness.oneHot, HonestWitness.fieldBool,
        chunk_values_ne]

theorem sum_instructionRaProduct_mul
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (i : Fin params.traceLength)
    (values : InstructionLookupAddress → F) :
    (∑ address : InstructionLookupAddress,
        (honest_witness (F := F) trace).instructionRaProduct address i *
          values address) =
      values (InstructionLookupAddress.ofBits
        (HonestWitness.lookupIndex (trace.rows i))) := by
  rw [show (∑ address : InstructionLookupAddress,
      (honest_witness (F := F) trace).instructionRaProduct address i *
        values address) =
      ∑ address : InstructionLookupAddress,
        HonestWitness.oneHot (F := F) address.val
            (HonestWitness.lookupIndex (trace.rows i)).toNat *
          values address by
        apply Finset.sum_congr rfl
        intro address _
        rw [honest_instructionRaProduct_eq_oneHot]]
  simpa using sum_oneHot_mul
    (InstructionLookupAddress.ofBits
      (HonestWitness.lookupIndex (trace.rows i))) values

theorem sum_lookupTableFlag_mul
    {F : Type u} [Field F] (row : JoltTraceRow)
    (values : JoltLookupTable → F) :
    (∑ table : JoltLookupTable,
        values table *
          HonestWitness.fieldBool
            (HonestWitness.lookupTable row.instruction == some table)) =
      match HonestWitness.lookupTable row.instruction with
      | some table => values table
      | none => 0 := by
  classical
  cases table_eq : HonestWitness.lookupTable row.instruction with
  | none =>
      simp [HonestWitness.fieldBool]
  | some selected =>
      rw [Finset.sum_eq_single selected]
      · simp [HonestWitness.fieldBool]
      · intro table _ table_ne
        have selected_ne : selected ≠ table := Ne.symm table_ne
        simp [HonestWitness.fieldBool, selected_ne]
      · simp

theorem lookupOutput_eq_zero_of_lookupTable_eq_none
    (row : JoltTraceRow)
    (table_eq : HonestWitness.lookupTable row.instruction = none) :
    HonestWitness.lookupOutput row = 0 := by
  generalize instruction_eq : row.instruction = instruction at table_eq ⊢
  cases instruction <;>
    simp [HonestWitness.lookupTable, HonestWitness.lookupOutput,
      HonestWitness.writesLookupOutput, HonestWitness.destination,
      instruction_eq] at table_eq ⊢

theorem lookupOutput_eq_selectedTable
    {params : JoltWitnessParams} {publicInputs : JoltPublicInputs params}
    {row : JoltTraceRow}
    {before after : SailJoltState}
    (valid : JoltTraceRow.Valid publicInputs row before after) :
    HonestWitness.lookupOutput row =
      match HonestWitness.lookupTable row.instruction with
      | some table =>
          JoltLookupTable.materializeEntry table
            (InstructionLookupAddress.ofBits
              (HonestWitness.lookupIndex row))
      | none => 0 := by
  cases table_eq : HonestWitness.lookupTable row.instruction with
  | none => exact lookupOutput_eq_zero_of_lookupTable_eq_none row table_eq
  | some table => exact valid.lookupOutput_eq_table table table_eq

end JoltConstraints.JoltConstraint.Completeness
