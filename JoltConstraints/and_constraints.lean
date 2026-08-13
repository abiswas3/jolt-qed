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
  unfold and_constraint JoltConstraint.Satisfied
  intro i
  change HonestWitness.fieldBool
      (HonestWitness.writesLookupOutput (trace.instrList i)) *
        (HonestWitness.fieldFromU64
            (HonestWitness.destinationRegisterValue
              (trace.postState i) (trace.instrList i)) -
          HonestWitness.fieldFromU64
            (HonestWitness.lookupOutput
              (trace.instrList i) (trace.preState i) (trace.postState i))) = 0
  cases h : HonestWitness.writesLookupOutput (trace.instrList i) <;>
    simp [HonestWitness.fieldBool, HonestWitness.lookupOutput, h]

end JoltConstraints
