import JoltConstraints.ConstraintCompleteness.Ram

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramAddressEqSelectedRamAddress
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramAddressEqSelectedRamAddress
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
    HonestWitness.fieldFromU64 (F := F) row.ramAddress -
        ∑ address : Fin params.ramK,
          (match HonestWitness.remappedRamAddress trace row with
          | some ramAddress =>
              HonestWitness.oneHot (F := F) address.val ramAddress
          | none => (0 : F)) *
            ((trace.metadata.lowestMemoryAddress.toNat +
              8 * address.val : Nat) : F) = 0
  cases remapped : HonestWitness.remappedRamAddress trace row with
  | none =>
      have address_zero : row.ramAddress = 0 :=
        valid.ramAddress_eq_zero (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      simp [address_zero, HonestWitness.fieldFromU64]
  | some ramAddress =>
      have address_bound : ramAddress < params.ramK :=
        valid.ramAddressBound ramAddress (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      let selected : Fin params.ramK := ⟨ramAddress, address_bound⟩
      have address_eq :
          row.ramAddress.toNat =
            trace.metadata.lowestMemoryAddress.toNat + 8 * ramAddress :=
        valid.ramAddress_eq ramAddress (by
          simpa [HonestWitness.remappedRamAddress] using remapped)
      have field_address_eq :
          HonestWitness.fieldFromU64 (F := F) row.ramAddress =
            ((trace.metadata.lowestMemoryAddress.toNat +
              8 * ramAddress : Nat) : F) := by
        simpa [HonestWitness.fieldFromU64] using
          congrArg (fun value : Nat => (value : F)) address_eq
      have selected_sum :
          (∑ address : Fin params.ramK,
              HonestWitness.oneHot (F := F) address.val ramAddress *
                ((trace.metadata.lowestMemoryAddress.toNat +
                  8 * address.val : Nat) : F)) =
            ((trace.metadata.lowestMemoryAddress.toNat +
              8 * ramAddress : Nat) : F) := by
        simpa [selected] using
          sum_oneHot_mul selected
            (fun address : Fin params.ramK =>
              ((trace.metadata.lowestMemoryAddress.toNat +
                8 * address.val : Nat) : F))
      rw [field_address_eq, selected_sum]
      ring

end JoltConstraints.JoltConstraint.Completeness
