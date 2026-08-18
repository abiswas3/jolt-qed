import JoltConstraints.ConstraintCompleteness.Ram

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramReadValueEqSelectedRamValue
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramReadValueEqSelectedRamValue
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have valid :
      JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
        (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  change
    HonestWitness.fieldFromU64 (F := F) row.ramReadValue -
        ∑ address : Fin params.ramK,
          (match HonestWitness.remappedRamAddress trace row with
          | some ramAddress =>
              HonestWitness.oneHot (F := F) address.val ramAddress
          | none => (0 : F)) *
            HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.memoryWord (trace.preState i)
                (trace.metadata.lowestMemoryAddress.toNat +
                  8 * address.val)) = 0
  cases remapped : HonestWitness.remappedRamAddress trace row with
  | none =>
      have read_zero : row.ramReadValue = 0 :=
        valid.ramReadValue_eq_zero (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      simp [read_zero, HonestWitness.fieldFromU64]
  | some ramAddress =>
      have address_bound : ramAddress < params.ramK :=
        valid.ramAddressBound ramAddress (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      let selected : Fin params.ramK := ⟨ramAddress, address_bound⟩
      have read_eq :
          row.ramReadValue =
            HonestWitness.memoryWord (trace.preState i)
              (trace.metadata.lowestMemoryAddress.toNat + 8 * ramAddress) :=
        valid.ramReadValue_eq ramAddress (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      have selected_sum :
          (∑ address : Fin params.ramK,
              HonestWitness.oneHot (F := F) address.val ramAddress *
                HonestWitness.fieldFromU64 (F := F)
                  (HonestWitness.memoryWord (trace.preState i)
                    (trace.metadata.lowestMemoryAddress.toNat +
                      8 * address.val))) =
            HonestWitness.fieldFromU64 (F := F)
              (HonestWitness.memoryWord (trace.preState i)
                (trace.metadata.lowestMemoryAddress.toNat +
                  8 * ramAddress)) := by
        simpa [selected] using
          sum_oneHot_mul selected
            (fun address : Fin params.ramK =>
              HonestWitness.fieldFromU64 (F := F)
                (HonestWitness.memoryWord (trace.preState i)
                  (trace.metadata.lowestMemoryAddress.toNat +
                    8 * address.val)))
      rw [read_eq, selected_sum]
      ring

end JoltConstraints.JoltConstraint.Completeness
