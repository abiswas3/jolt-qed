import JoltConstraints.ConstraintCompleteness.Encoding

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem leftInstructionInputEqSelectedOperands
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .leftInstructionInputEqSelectedOperands
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  change
    HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.instructionInputs row).1 -
        (HonestWitness.fieldBool
              ((HonestWitness.lookupFirstSource row.instruction).isSome) *
            HonestWitness.fieldFromU64 (F := F) row.rs1Value +
          HonestWitness.fieldBool (HonestWitness.leftIsPC row.instruction) *
            HonestWitness.fieldFromU64 (F := F) row.metadata.unexpandedPC) = 0
  generalize instruction_eq : row.instruction = instruction
  cases instruction <;>
    simp [HonestWitness.instructionInputs, HonestWitness.lookupFirstSource,
      HonestWitness.firstSource, HonestWitness.leftIsPC,
      HonestWitness.fieldBool, HonestWitness.fieldFromU64,
      instruction_eq]

end JoltConstraints.JoltConstraint.Completeness
