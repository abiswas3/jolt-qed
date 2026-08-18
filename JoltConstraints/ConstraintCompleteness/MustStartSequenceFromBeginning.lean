import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem mustStartSequenceFromBeginning
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .mustStartSequenceFromBeginning trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  let witness : JoltWitness params F := honest_witness (F := F) trace
  change JoltConstraint.Satisfied .mustStartSequenceFromBeginning trace.metadata.toJoltPublicInputs witness
  unfold JoltConstraint.Satisfied
  intro i
  let current := trace.rows i
  have nextVirtual_from_trace :
      witness.virtual .nextIsVirtual i =
        HonestWitness.fieldBool (match HonestWitness.nextMetadata trace i with
          | some metadata => HonestWitness.isVirtual metadata
          | none => false) := by
    rfl
  have nextFirst_from_trace :
      witness.virtual .nextIsFirstInSequence i =
        HonestWitness.fieldBool (match HonestWitness.nextMetadata trace i with
          | some metadata => metadata.isFirstInSequence
          | none => false) := by
    rfl
  have doNotUpdate_from_trace :
      witness.opFlag .doNotUpdateUnexpandedPC i =
        HonestWitness.fieldBool
          (HonestWitness.doNotUpdateUnexpandedPC
            current.instruction current.metadata) := by
    rfl
  rw [nextVirtual_from_trace, nextFirst_from_trace, doNotUpdate_from_trace]
  cases hnext : HonestWitness.nextTraceIndex i with
  | none =>
      simp [HonestWitness.nextMetadata, hnext, HonestWitness.fieldBool]
  | some j =>
      let next := trace.rows j
      have pair_valid : JoltTracePair.Valid current next := by
        simpa [current, next] using trace.pairValid i j hnext
      have next_valid := trace.rowValid j
      have nextMetadata_eq :
          HonestWitness.nextMetadata trace i = some next.metadata := by
        simp [HonestWitness.nextMetadata, hnext, next,
          HonestTrace.rowMetadata, ExecutionTrace.rowMetadata]
      rw [nextMetadata_eq]
      change
        (HonestWitness.fieldBool (HonestWitness.isVirtual next.metadata) -
          HonestWitness.fieldBool next.metadata.isFirstInSequence) *
        (1 - HonestWitness.fieldBool
          (HonestWitness.doNotUpdateUnexpandedPC
            current.instruction current.metadata)) = 0
      cases nextVirtual : HonestWitness.isVirtual next.metadata
      · cases nextFirst : next.metadata.isFirstInSequence
        · simp [HonestWitness.fieldBool]
        · have : HonestWitness.isVirtual next.metadata = true := by
            apply next_valid.firstInSequence_isVirtual
            simpa [next] using nextFirst
          simp [nextVirtual] at this
      · cases nextFirst : next.metadata.isFirstInSequence
        · have doNotUpdate :=
            pair_valid.sequenceStart nextVirtual nextFirst
          simp [HonestWitness.fieldBool, doNotUpdate]
        · simp [HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
