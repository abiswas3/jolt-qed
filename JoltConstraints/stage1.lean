import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage1` is only a classifier on the global `JoltConstraint` type. It carries
no sumcheck, batching, or prover-stage semantics. It selects the 19
equality-conditional RV64 constraints tested by Rust's `SpartanOuter`
sumcheck. Rust tests the three product constraints in Stage 2.
-/

def stage1 : JoltConstraint → Bool
  | .ramAddrEqRs1PlusImmIfLoadStore => true
  | .ramAddrEqZeroIfNotLoadStore => true
  | .ramReadEqRamWriteIfLoad => true
  | .ramReadEqRdWriteIfLoad => true
  | .rs2EqRamWriteIfStore => true
  | .leftLookupZeroUnlessAddSubMul => true
  | .leftLookupEqLeftInputOtherwise => true
  | .rightLookupAdd => true
  | .rightLookupSub => true
  | .rightLookupEqProductIfMul => true
  | .rightLookupEqRightInputOtherwise => true
  | .assertLookupOne => true
  | .rdWriteEqLookupIfWriteLookupToRD => true
  | .rdWriteEqPCPlusConstIfWritePCToRD => true
  | .nextUnexpandedPCEqLookupIfShouldJump => true
  | .nextUnexpandedPCEqPCPlusImmIfShouldBranch => true
  | .nextUnexpandedPCUpdateOtherwise => true
  | .nextPCEqPCPlusOneIfInline => true
  | .mustStartSequenceFromBeginning => true
  | .productEqLeftInputMulRightInput => false
  | .shouldBranchEqLookupOutputMulBranch => false
  | .shouldJumpEqJumpMulNotNextIsNoop => false
  | .ramReadValueEqSelectedRamValue => false
  | .ramWriteValueEqSelectedRamValuePlusIncrement => false
  | .ramAddressEqSelectedRamAddress => false
  | .ramFinalValueEqPublicIo => false

end JoltConstraints
