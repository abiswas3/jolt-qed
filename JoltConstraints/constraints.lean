import JoltConstraints.witness

namespace JoltConstraints

universe u

inductive JoltConstraint where
  | rdWriteEqLookupIfWriteLookupToRD
  deriving DecidableEq, Repr

private def rdWriteEqLookupIfWriteLookupToRD_satisfied {T : Nat} {F : Type u} [Field F]
(witness : JoltWitness T F)
: Prop := 
∀ i : Fin T,
      witness.writeLookupOutputToRD i *
        (witness.rdWriteValue i - witness.lookupOutput i) = 0


def JoltConstraint.Satisfied
    {T : Nat} {F : Type u} [Field F]
    (constraint : JoltConstraint) (witness : JoltWitness T F) : Prop :=
  match constraint with
  | .rdWriteEqLookupIfWriteLookupToRD => rdWriteEqLookupIfWriteLookupToRD_satisfied witness
    
end JoltConstraints
