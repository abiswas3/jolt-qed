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
  let instruction := trace.instrList i
  let before := trace.preState i

  have loadFlag_from_trace :
      witness.opFlag .load i =
        HonestWitness.fieldBool (HonestWitness.isLoad instruction) := by
    rfl
  have storeFlag_from_trace :
      witness.opFlag .store i =
        HonestWitness.fieldBool (HonestWitness.isStore instruction) := by
    rfl
  have ramAddress_from_trace :
      witness.virtual .ramAddress i =
        HonestWitness.fieldFromU64
          ((HonestWitness.ramAccessAddress instruction before).getD 0) := by
    rfl

  rw [loadFlag_from_trace, storeFlag_from_trace, ramAddress_from_trace]
  cases instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.isLoad, HonestWitness.isStore,
      HonestWitness.ramAccessAddress, HonestWitness.fieldFromU64]

end JoltConstraints.JoltConstraint.Completeness
