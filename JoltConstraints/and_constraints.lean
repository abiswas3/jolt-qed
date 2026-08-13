import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints

universe u

/-
Given witness we prove that this specific JoltConstraint is satisfied.
-/ 
def and_constraint
    {T : Nat} {F : Type u} [Field F]
    (witness : JoltWitness T F) : Prop :=
  JoltConstraint.Satisfied .rdWriteEqLookupIfWriteLookupToRD witness

/-
The completeness theorem says when the wintess:= honest_witness constructed from an honest trace
-/ 
theorem and_completeness
    {T : Nat} {F : Type u} [Field F]
    (trace : HonestTrace T) :
    and_constraint (honest_witness (F := F) trace) := by
  -- Let `witness` denote the witness obtained by filling every column from the
  -- honest execution trace.
  let witness : JoltWitness T F := honest_witness (F := F) trace
  change and_constraint witness

  -- The constraint is row-wise, so fix an arbitrary trace row.
  unfold and_constraint 
  unfold JoltConstraint.Satisfied
  intro i
  let instruction := trace.instrList i
  let before := trace.preState i
  let after := trace.postState i

  -- Honest witness generation fills the write-lookup-output flag from the
  -- instruction at this row.
  have writeFlag_from_trace :
      witness.writeLookupOutputToRD i =
        HonestWitness.fieldBool
          (HonestWitness.writesLookupOutput instruction) := by
    rfl

  -- It fills the claimed destination-register value from the post-state.
  have rdWriteValue_from_trace :
      witness.rdWriteValue i =
        HonestWitness.fieldFromU64
          (HonestWitness.destinationRegisterValue after instruction) := by
    rfl

  -- It also fills the lookup-output column with the lookup output determined
  -- by this instruction and its pre- and post-states.
  have lookupOutput_from_trace :
      witness.lookupOutput i =
        HonestWitness.fieldFromU64
          (HonestWitness.lookupOutput instruction before after) := by
    rfl

  -- Substitute those three honest column values into the constraint equation.
  rw [writeFlag_from_trace, rdWriteValue_from_trace, lookupOutput_from_trace]

  -- If the instruction does not write the lookup output, the flag is zero. If
  -- it does, the lookup output is exactly the destination value in the
  -- post-state, so the difference in the constraint is zero.
  cases h : HonestWitness.writesLookupOutput instruction <;>
    simp [HonestWitness.fieldBool, HonestWitness.lookupOutput, h]

end JoltConstraints
