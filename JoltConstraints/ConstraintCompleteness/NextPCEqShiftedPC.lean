import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextPCEqShiftedPC
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextPCEqShiftedPC
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  cases h : HonestWitness.nextTraceIndex i <;>
  simp [HonestWitness.shiftedColumn, HonestWitness.nextMetadata,
    honest_witness, h]

end JoltConstraints.JoltConstraint.Completeness
