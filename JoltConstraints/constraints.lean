import JoltConstraints.trace

namespace JoltConstraints

universe u

open scoped BigOperators

-- NOTE: We are assuming that the bytecode is fixed and public for now.

/-!
# Jolt witness constraints
These are the set of equations that restrict the space of acceptable witnesses.
-/

inductive JoltConstraint where
  | ramAddrEqRs1PlusImmIfLoadStore
  | ramAddrEqZeroIfNotLoadStore
  | ramReadEqRamWriteIfLoad
  | ramReadEqRdWriteIfLoad
  | rs2EqRamWriteIfStore
  | leftLookupZeroUnlessAddSubMul
  | leftLookupEqLeftInputOtherwise
  | rightLookupAdd
  | rightLookupSub
  | rightLookupEqProductIfMul
  | rightLookupEqRightInputOtherwise
  | assertLookupOne
  | rdWriteEqLookupIfWriteLookupToRD
  | rdWriteEqPCPlusConstIfWritePCToRD
  | nextUnexpandedPCEqLookupIfShouldJump
  | nextUnexpandedPCEqPCPlusImmIfShouldBranch
  | nextUnexpandedPCUpdateOtherwise
  | nextPCEqPCPlusOneIfInline
  | mustStartSequenceFromBeginning
  -- Stage 2: the three identities batched by Spartan product virtualization.
  | productEqLeftInputMulRightInput
  | shouldBranchEqLookupOutputMulBranch
  | shouldJumpEqJumpMulNotNextIsNoop
  -- Stage 2: three RAM sumchecks, with the gamma-batched read/write relation
  -- split into its two underlying identities.
  | ramReadValueEqSelectedRamValue
  | ramWriteValueEqSelectedRamValuePlusIncrement
  | ramAddressEqSelectedRamAddress
  | ramFinalValueEqPublicIo
  -- Stage 3: the five components batched by Spartan shift.
  | nextUnexpandedPCEqShiftedUnexpandedPC
  | nextPCEqShiftedPC
  | nextIsVirtualEqShiftedVirtualInstruction
  | nextIsFirstInSequenceEqShiftedFirstInSequence
  | nextIsNoopEqShiftedNoop
  -- Stage 3: the two components batched by instruction-input virtualization.
  | leftInstructionInputEqSelectedOperands
  | rightInstructionInputEqSelectedOperands
  -- Stage 4: the three components batched by register read/write checking.
  | rs1ValueEqSelectedRegistersVal
  | rs2ValueEqSelectedRegistersVal
  | rdWriteValueEqSelectedRegistersValPlusIncrement
  -- Stage 4: the two components batched by RAM value checking.
  | ramValEqInitialValuePlusPriorIncrements
  | ramValFinalEqInitialValuePlusAllIncrements
  -- Stage 5: the three gamma components of instruction read-RAF.
  | lookupOutputEqInstructionReadRaf
  | leftLookupOperandEqInstructionReadRaf
  | rightLookupOperandEqInstructionReadRaf
  -- Stage 5: register-state evaluation from prior destination increments.
  | registersValEqPriorWrites
  -- Stage 6: the three RA-family components of Rust's one booleanity
  -- sumcheck. These are witness identities, not three separate sumchecks.
  | instructionRaBooleanity
  | bytecodeRaBooleanity
  | ramRaBooleanity
  -- Stage 6: virtual instruction-RA chunks are products of their contiguous
  -- committed subchunks.
  | instructionRaVirtualization
  | ramRaVirtualization
  | ramHammingWeightBooleanity
  -- Stage 6: coefficient identities inside Rust's single fixed/public
  -- bytecode read-RAF relation.
  | unexpandedPCEqBytecodeReadRaf
  | immEqBytecodeReadRaf
  | circuitFlagsEqBytecodeReadRaf
  | pcEqBytecodeReadRafAddress
  | instructionFlagsEqBytecodeReadRaf
  | rs1RaEqBytecodeReadRaf
  | rs2RaEqBytecodeReadRaf
  | rdWaEqBytecodeReadRaf
  | instructionRafFlagEqBytecodeReadRaf
  | lookupTableFlagsEqBytecodeReadRaf
  | initialBytecodeRaEqEntry
  deriving DecidableEq, Repr

end JoltConstraints
