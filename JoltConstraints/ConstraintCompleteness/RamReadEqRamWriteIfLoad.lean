import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem ramReadEqRamWriteIfLoad
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .ramReadEqRamWriteIfLoad
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .ramReadEqRamWriteIfLoad witness

  unfold JoltConstraint.Satisfied
  intro i
  let instruction := trace.instrList i
  let before := trace.preState i
  let after := trace.postState i

  have loadFlag_from_trace :
      witness.opFlag .load i =
        HonestWitness.fieldBool (HonestWitness.isLoad instruction) := by
    rfl
  have ramRead_from_trace :
      witness.virtual .ramReadValue i =
        HonestWitness.fieldFromU64
          (HonestWitness.ramReadValue instruction before) := by
    rfl
  have ramWrite_from_trace :
      witness.virtual .ramWriteValue i =
        HonestWitness.fieldFromU64
          (HonestWitness.ramWriteValue instruction before after) := by
    rfl

  rw [loadFlag_from_trace, ramRead_from_trace, ramWrite_from_trace]
  cases instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.isLoad,
      HonestWitness.ramWriteValue]

end JoltConstraints.JoltConstraint.Completeness
