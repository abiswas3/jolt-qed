import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage3` classifies the seven Stage 3 witness identities in Rust:

* `SpartanShift` gamma-batches five non-wrapping next-row identities; and
* `InstructionInputVirtualization` gamma-batches the left- and right-input
  selection identities.

`RegistersClaimReduction` is a claim reduction, so it is intentionally not a
`JoltConstraint`.
-/

def stage3 : JoltConstraint → Bool
  | .nextUnexpandedPCEqShiftedUnexpandedPC
  | .nextPCEqShiftedPC
  | .nextIsVirtualEqShiftedVirtualInstruction
  | .nextIsFirstInSequenceEqShiftedFirstInSequence
  | .nextIsNoopEqShiftedNoop
  | .leftInstructionInputEqSelectedOperands
  | .rightInstructionInputEqSelectedOperands => true
  | _ => false

end JoltConstraints
