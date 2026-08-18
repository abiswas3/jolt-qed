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
import JoltConstraints.ConstraintCompleteness.NextUnexpandedPCEqShiftedUnexpandedPC
import JoltConstraints.ConstraintCompleteness.NextPCEqShiftedPC
import JoltConstraints.ConstraintCompleteness.NextIsVirtualEqShiftedVirtualInstruction
import JoltConstraints.ConstraintCompleteness.NextIsFirstInSequenceEqShiftedFirstInSequence
import JoltConstraints.ConstraintCompleteness.NextIsNoopEqShiftedNoop
import JoltConstraints.ConstraintCompleteness.LeftInstructionInputEqSelectedOperands
import JoltConstraints.ConstraintCompleteness.RightInstructionInputEqSelectedOperands
import JoltConstraints.ConstraintCompleteness.Rs1ValueEqSelectedRegistersVal
import JoltConstraints.ConstraintCompleteness.Rs2ValueEqSelectedRegistersVal
import JoltConstraints.ConstraintCompleteness.RdWriteValueEqSelectedRegistersValPlusIncrement
import JoltConstraints.ConstraintCompleteness.RamValEqInitialValuePlusPriorIncrements
import JoltConstraints.ConstraintCompleteness.RamValFinalEqInitialValuePlusAllIncrements
import JoltConstraints.ConstraintCompleteness.LookupOutputEqInstructionReadRaf
import JoltConstraints.ConstraintCompleteness.LeftLookupOperandEqInstructionReadRaf
import JoltConstraints.ConstraintCompleteness.RightLookupOperandEqInstructionReadRaf
import JoltConstraints.ConstraintCompleteness.RegistersValEqPriorWrites
import JoltConstraints.ConstraintCompleteness.InstructionRaBooleanity
import JoltConstraints.ConstraintCompleteness.BytecodeRaBooleanity
import JoltConstraints.ConstraintCompleteness.RamRaBooleanity
import JoltConstraints.ConstraintCompleteness.InstructionRaVirtualization
import JoltConstraints.ConstraintCompleteness.RamRaVirtualization
import JoltConstraints.ConstraintCompleteness.RamHammingWeightBooleanity

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
  | nextUnexpandedPCEqShiftedUnexpandedPC =>
      exact nextUnexpandedPCEqShiftedUnexpandedPC trace
  | nextPCEqShiftedPC => exact nextPCEqShiftedPC trace
  | nextIsVirtualEqShiftedVirtualInstruction =>
      exact nextIsVirtualEqShiftedVirtualInstruction trace
  | nextIsFirstInSequenceEqShiftedFirstInSequence =>
      exact nextIsFirstInSequenceEqShiftedFirstInSequence trace
  | nextIsNoopEqShiftedNoop => exact nextIsNoopEqShiftedNoop trace
  | leftInstructionInputEqSelectedOperands =>
      exact leftInstructionInputEqSelectedOperands trace
  | rightInstructionInputEqSelectedOperands =>
      exact rightInstructionInputEqSelectedOperands trace
  | rs1ValueEqSelectedRegistersVal =>
      exact rs1ValueEqSelectedRegistersVal trace
  | rs2ValueEqSelectedRegistersVal =>
      exact rs2ValueEqSelectedRegistersVal trace
  | rdWriteValueEqSelectedRegistersValPlusIncrement =>
      exact rdWriteValueEqSelectedRegistersValPlusIncrement trace
  | ramValEqInitialValuePlusPriorIncrements =>
      exact ramValEqInitialValuePlusPriorIncrements trace
  | ramValFinalEqInitialValuePlusAllIncrements =>
      exact ramValFinalEqInitialValuePlusAllIncrements trace
  | lookupOutputEqInstructionReadRaf =>
      exact lookupOutputEqInstructionReadRaf trace
  | leftLookupOperandEqInstructionReadRaf =>
      exact leftLookupOperandEqInstructionReadRaf trace
  | rightLookupOperandEqInstructionReadRaf =>
      exact rightLookupOperandEqInstructionReadRaf trace
  | registersValEqPriorWrites => exact registersValEqPriorWrites trace
  | instructionRaBooleanity => exact instructionRaBooleanity trace
  | bytecodeRaBooleanity => exact bytecodeRaBooleanity trace
  | ramRaBooleanity => exact ramRaBooleanity trace
  | instructionRaVirtualization => exact instructionRaVirtualization trace
  | ramRaVirtualization => exact ramRaVirtualization trace
  | ramHammingWeightBooleanity => exact ramHammingWeightBooleanity trace

end JoltConstraints.JoltConstraint.Completeness
