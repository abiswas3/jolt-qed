import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage1` is only a classifier on the global `JoltConstraint` type. It carries
no sumcheck, batching, or prover-stage semantics. For the current model, all
22 constraints of the full RV64 trace R1CS belong to this set.
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
  | .productEqLeftInputMulRightInput => true
  | .shouldBranchEqLookupOutputMulBranch => true
  | .shouldJumpEqJumpMulNotNextIsNoop => true

end JoltConstraints
