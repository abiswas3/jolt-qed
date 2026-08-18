import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextIsFirstInSequenceEqShiftedFirstInSequence
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextIsFirstInSequenceEqShiftedFirstInSequence
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  cases h : HonestWitness.nextTraceIndex i <;>
  simp [HonestWitness.shiftedColumn, HonestWitness.nextMetadata,
    HonestWitness.circuitFlagValue, HonestWitness.fieldBool,
    JoltWitness.opFlag, honest_witness, h]
  ring_nf

end JoltConstraints.JoltConstraint.Completeness
