import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem nextIsNoopEqShiftedNoop
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .nextIsNoopEqShiftedNoop
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  cases h : HonestWitness.nextTraceIndex i <;>
  simp [HonestWitness.shiftedColumn, HonestWitness.nextInstruction,
    HonestWitness.instructionFlagValue, HonestWitness.fieldBool,
    JoltWitness.instructionFlag, honest_witness, h]
  ring_nf

end JoltConstraints.JoltConstraint.Completeness
