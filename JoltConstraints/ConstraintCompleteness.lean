import JoltConstraints.ConstraintCompleteness.RamAddrEqRs1PlusImmIfLoadStore
import JoltConstraints.ConstraintCompleteness.RamAddrEqZeroIfNotLoadStore
import JoltConstraints.ConstraintCompleteness.RamReadEqRamWriteIfLoad
import JoltConstraints.ConstraintCompleteness.RamReadEqRdWriteIfLoad
import JoltConstraints.ConstraintCompleteness.Rs2EqRamWriteIfStore
import JoltConstraints.ConstraintCompleteness.LeftLookupZeroUnlessAddSubMul
import JoltConstraints.ConstraintCompleteness.LeftLookupEqLeftInputOtherwise
import JoltConstraints.ConstraintCompleteness.RightLookupAdd
import JoltConstraints.ConstraintCompleteness.RightLookupSub
import JoltConstraints.ConstraintCompleteness.RightLookupEqProductIfMul
import JoltConstraints.ConstraintCompleteness.RightLookupEqRightInputOtherwise
import JoltConstraints.ConstraintCompleteness.AssertLookupOne
import JoltConstraints.ConstraintCompleteness.RdWriteEqLookupIfWriteLookupToRD
import JoltConstraints.ConstraintCompleteness.RdWriteEqPCPlusConstIfWritePCToRD
import JoltConstraints.ConstraintCompleteness.NextUnexpandedPCEqLookupIfShouldJump
import JoltConstraints.ConstraintCompleteness.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import JoltConstraints.ConstraintCompleteness.NextUnexpandedPCUpdateOtherwise
import JoltConstraints.ConstraintCompleteness.NextPCEqPCPlusOneIfInline
import JoltConstraints.ConstraintCompleteness.MustStartSequenceFromBeginning
import JoltConstraints.ConstraintCompleteness.ProductEqLeftInputMulRightInput
import JoltConstraints.ConstraintCompleteness.ShouldBranchEqLookupOutputMulBranch
import JoltConstraints.ConstraintCompleteness.ShouldJumpEqJumpMulNotNextIsNoop
import JoltConstraints.ConstraintCompleteness.RamReadValueEqSelectedRamValue
import JoltConstraints.ConstraintCompleteness.RamWriteValueEqSelectedRamValuePlusIncrement
import JoltConstraints.ConstraintCompleteness.RamAddressEqSelectedRamAddress
import JoltConstraints.ConstraintCompleteness.RamFinalValueEqPublicIo

namespace JoltConstraints.JoltConstraint.Completeness

universe u

/-!
The constructor-specific lemmas are kept separate so that each constraint can
be completed and reviewed independently. This theorem is deliberately only a
case split: it contains no additional constraint reasoning.
-/

theorem honest_witness_satisfies
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) (constraint : JoltConstraint) :
    constraint.Satisfied trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  cases constraint with
  | ramAddrEqRs1PlusImmIfLoadStore =>
      exact ramAddrEqRs1PlusImmIfLoadStore trace
  | ramAddrEqZeroIfNotLoadStore => exact ramAddrEqZeroIfNotLoadStore trace
  | ramReadEqRamWriteIfLoad => exact ramReadEqRamWriteIfLoad trace
  | ramReadEqRdWriteIfLoad => exact ramReadEqRdWriteIfLoad trace
  | rs2EqRamWriteIfStore => exact rs2EqRamWriteIfStore trace
  | leftLookupZeroUnlessAddSubMul => exact leftLookupZeroUnlessAddSubMul trace
  | leftLookupEqLeftInputOtherwise => exact leftLookupEqLeftInputOtherwise trace
  | rightLookupAdd => exact rightLookupAdd trace
  | rightLookupSub => exact rightLookupSub trace
  | rightLookupEqProductIfMul => exact rightLookupEqProductIfMul trace
  | rightLookupEqRightInputOtherwise =>
      exact rightLookupEqRightInputOtherwise trace
  | assertLookupOne => exact assertLookupOne trace
  | rdWriteEqLookupIfWriteLookupToRD =>
      exact rdWriteEqLookupIfWriteLookupToRD trace
  | rdWriteEqPCPlusConstIfWritePCToRD =>
      exact rdWriteEqPCPlusConstIfWritePCToRD trace
  | nextUnexpandedPCEqLookupIfShouldJump =>
      exact nextUnexpandedPCEqLookupIfShouldJump trace
  | nextUnexpandedPCEqPCPlusImmIfShouldBranch =>
      exact nextUnexpandedPCEqPCPlusImmIfShouldBranch trace
  | nextUnexpandedPCUpdateOtherwise =>
      exact nextUnexpandedPCUpdateOtherwise trace
  | nextPCEqPCPlusOneIfInline => exact nextPCEqPCPlusOneIfInline trace
  | mustStartSequenceFromBeginning => exact mustStartSequenceFromBeginning trace
  | productEqLeftInputMulRightInput =>
      exact productEqLeftInputMulRightInput trace
  | shouldBranchEqLookupOutputMulBranch =>
      exact shouldBranchEqLookupOutputMulBranch trace
  | shouldJumpEqJumpMulNotNextIsNoop =>
      exact shouldJumpEqJumpMulNotNextIsNoop trace
  | ramReadValueEqSelectedRamValue =>
      exact ramReadValueEqSelectedRamValue trace
  | ramWriteValueEqSelectedRamValuePlusIncrement =>
      exact ramWriteValueEqSelectedRamValuePlusIncrement trace
  | ramAddressEqSelectedRamAddress =>
      exact ramAddressEqSelectedRamAddress trace
  | ramFinalValueEqPublicIo => exact ramFinalValueEqPublicIo trace

end JoltConstraints.JoltConstraint.Completeness
