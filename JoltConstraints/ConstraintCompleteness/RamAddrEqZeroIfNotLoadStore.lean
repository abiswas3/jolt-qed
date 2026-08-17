import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramAddrEqZeroIfNotLoadStore
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramAddrEqZeroIfNotLoadStore
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .ramAddrEqZeroIfNotLoadStore witness

  unfold JoltConstraint.Satisfied
  intro i
  have loadFlag_from_trace :
      witness.opFlag .load i =
        HonestWitness.fieldBool
          (HonestWitness.isLoad (trace.rows i).instruction) := by
    rfl
  have storeFlag_from_trace :
      witness.opFlag .store i =
        HonestWitness.fieldBool
          (HonestWitness.isStore (trace.rows i).instruction) := by
    rfl
  have ramAddress_from_trace :
      witness.virtual .ramAddress i =
        HonestWitness.fieldFromU64 (trace.rows i).ramAddress := by
    rfl
  rw [loadFlag_from_trace, storeFlag_from_trace, ramAddress_from_trace]
  rcases hrow : trace.rows i with ⟨instruction, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp [HonestWitness.fieldBool, HonestWitness.isLoad,
      HonestWitness.isStore, JoltTraceRow.ramAddress,
      CapturedState.ramAddress, HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
