import JoltConstraints.ConstraintCompleteness.Ram

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem sum_registerAddressIndicator_mul
    {F : Type u} [Field F]
    (selected : Option RegisterAddress) (values : RegisterAddress → F) :
    (∑ address : RegisterAddress,
        HonestWitness.registerAddressIndicator selected address *
          values address) =
      match selected with
      | some address => values address
      | none => 0 := by
  classical
  cases selected with
  | none =>
      simp [HonestWitness.registerAddressIndicator]
  | some selected =>
      rw [Finset.sum_eq_single selected]
      · simp [HonestWitness.registerAddressIndicator,
          HonestWitness.fieldBool]
      · intro address _ address_ne
        have selected_ne : selected ≠ address := Ne.symm address_ne
        simp [HonestWitness.registerAddressIndicator,
          HonestWitness.fieldBool, selected_ne]
      · simp

end JoltConstraints.JoltConstraint.Completeness
