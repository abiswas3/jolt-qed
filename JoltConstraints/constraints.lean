import JoltConstraints.witness

namespace JoltConstraints

universe u

-- NOTE: We are assuming that the bytecode is fixed and public for now.
-- Constraints for Jolt's committed-program mode are not modelled here.

inductive JoltConstraint where
  | leftLookupEqLeftInputOtherwise
  | rightLookupEqRightInputOtherwise
  | rdWriteEqLookupIfWriteLookupToRD
  deriving DecidableEq, Repr

private def leftLookupEqLeftInputOtherwise_satisfied
    {T : Nat} {F : Type u} [Field F]
    (witness : JoltWitness T F) : Prop :=
  ∀ i : Fin T,
    (1 - witness.opFlag .addOperands i
      - witness.opFlag .subtractOperands i
      - witness.opFlag .multiplyOperands i) *
        (witness.leftLookupOperand i - witness.leftInstructionInput i) = 0

private def rightLookupEqRightInputOtherwise_satisfied
    {T : Nat} {F : Type u} [Field F]
    (witness : JoltWitness T F) : Prop :=
  ∀ i : Fin T,
    (1 - witness.opFlag .addOperands i
      - witness.opFlag .subtractOperands i
      - witness.opFlag .multiplyOperands i
      - witness.opFlag .advice i) *
        (witness.rightLookupOperand i - witness.rightInstructionInput i) = 0

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
  | .leftLookupEqLeftInputOtherwise => leftLookupEqLeftInputOtherwise_satisfied witness
  | .rightLookupEqRightInputOtherwise => rightLookupEqRightInputOtherwise_satisfied witness
  | .rdWriteEqLookupIfWriteLookupToRD => rdWriteEqLookupIfWriteLookupToRD_satisfied witness
    
end JoltConstraints
