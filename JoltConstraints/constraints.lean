import JoltConstraints.trace

namespace JoltConstraints

universe u

open scoped BigOperators

-- NOTE: We are assuming that the bytecode is fixed and public for now.
-- Constraints for Jolt's committed-program mode are not modelled here.

/-!
# Jolt witness constraints

Each constructor names one unbatched identity tested by a Jolt sumcheck. The
48 constructors are grouped by Rust proving stage as 19 in Stage 1, seven in
Stage 2, seven in Stage 3, five in Stage 4, four in Stage 5, and three currently
modelled booleanity components plus instruction-RA virtualization in Stage 6.
Claim reductions, batching, and sumcheck round-splitting
machinery are intentionally not included.
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
  deriving DecidableEq, Repr

private def ramAddrEqRs1PlusImmIfLoadStore_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (witness.opFlag .load i + witness.opFlag .store i) *
        (witness.virtual .ramAddress i - witness.rs1Value i -
          witness.virtual .imm i) = 0

private def ramAddrEqZeroIfNotLoadStore_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (1 - witness.opFlag .load i - witness.opFlag .store i) *
        witness.virtual .ramAddress i = 0

private def ramReadEqRamWriteIfLoad_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .load i *
        (witness.virtual .ramReadValue i - witness.virtual .ramWriteValue i) = 0

private def ramReadEqRdWriteIfLoad_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .load i *
        (witness.virtual .ramReadValue i - witness.rdWriteValue i) = 0

private def rs2EqRamWriteIfStore_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .store i *
        (witness.rs2Value i - witness.virtual .ramWriteValue i) = 0

private def leftLookupZeroUnlessAddSubMul_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (witness.opFlag .addOperands i
      + witness.opFlag .subtractOperands i
      + witness.opFlag .multiplyOperands i) *
        witness.leftLookupOperand i = 0

private def leftLookupEqLeftInputOtherwise_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (1 - witness.opFlag .addOperands i
      - witness.opFlag .subtractOperands i
      - witness.opFlag .multiplyOperands i) *
        (witness.leftLookupOperand i - witness.leftInstructionInput i) = 0

private def rightLookupAdd_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .addOperands i *
        (witness.rightLookupOperand i - witness.leftInstructionInput i -
          witness.rightInstructionInput i) = 0

private def rightLookupSub_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .subtractOperands i *
        (witness.rightLookupOperand i - witness.leftInstructionInput i +
          witness.rightInstructionInput i - ((2 ^ Xlen : Nat) : F)) = 0

private def rightLookupEqProductIfMul_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .multiplyOperands i *
        (witness.rightLookupOperand i - witness.virtual .product i) = 0

private def rightLookupEqRightInputOtherwise_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (1 - witness.opFlag .addOperands i
      - witness.opFlag .subtractOperands i
      - witness.opFlag .multiplyOperands i
      - witness.opFlag .advice i) *
        (witness.rightLookupOperand i - witness.rightInstructionInput i) = 0

private def assertLookupOne_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .assert i * (witness.lookupOutput i - 1) = 0

private def rdWriteEqLookupIfWriteLookupToRD_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.writeLookupOutputToRD i *
        (witness.rdWriteValue i - witness.lookupOutput i) = 0

private def rdWriteEqPCPlusConstIfWritePCToRD_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .jump i *
        (witness.rdWriteValue i - witness.virtual .unexpandedPC i - 4 +
          2 * witness.opFlag .isCompressed i) = 0

private def nextUnexpandedPCEqLookupIfShouldJump_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .shouldJump i *
        (witness.virtual .nextUnexpandedPC i - witness.lookupOutput i) = 0

private def nextUnexpandedPCEqPCPlusImmIfShouldBranch_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .shouldBranch i *
        (witness.virtual .nextUnexpandedPC i - witness.virtual .unexpandedPC i -
          witness.virtual .imm i) = 0

private def nextUnexpandedPCUpdateOtherwise_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (1 - witness.virtual .shouldBranch i - witness.opFlag .jump i) *
        (witness.virtual .nextUnexpandedPC i - witness.virtual .unexpandedPC i - 4 +
          4 * witness.opFlag .doNotUpdateUnexpandedPC i +
          2 * witness.opFlag .isCompressed i) = 0

private def nextPCEqPCPlusOneIfInline_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (witness.opFlag .virtualInstruction i - witness.opFlag .isLastInSequence i) *
        (witness.virtual .nextPC i - witness.virtual .pc i - 1) = 0

private def mustStartSequenceFromBeginning_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    (witness.virtual .nextIsVirtual i - witness.virtual .nextIsFirstInSequence i) *
        (1 - witness.opFlag .doNotUpdateUnexpandedPC i) = 0

private def productEqLeftInputMulRightInput_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.leftInstructionInput i * witness.rightInstructionInput i -
        witness.virtual .product i = 0

private def shouldBranchEqLookupOutputMulBranch_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.lookupOutput i * witness.instructionFlag .branch i -
        witness.virtual .shouldBranch i = 0

private def shouldJumpEqJumpMulNotNextIsNoop_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.opFlag .jump i * (1 - witness.virtual .nextIsNoop i) -
        witness.virtual .shouldJump i = 0

private def ramReadValueEqSelectedRamValue_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.ramReadValue i -
        ∑ address : Fin params.ramK,
          witness.ramRa address i * witness.ramVal address i = 0

private def ramWriteValueEqSelectedRamValuePlusIncrement_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.ramWriteValue i -
        ∑ address : Fin params.ramK,
          witness.ramRa address i *
            (witness.ramVal address i + witness.ramInc i) = 0

private def ramAddressEqSelectedRamAddress_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.ramAddress i -
        ∑ address : Fin params.ramK,
          witness.ramRa address i *
            ((publicInputs.lowestMemoryAddress.toNat + 8 * address.val : Nat) : F) = 0

private def ramFinalValueEqPublicIo_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  ∀ address : Fin params.ramK,
    (if publicInputs.ramOutputMask address then (1 : F) else 0) *
        (witness.ramValFinal address -
          (publicInputs.ramOutputValue address).toNat) = 0

private def nextUnexpandedPCEqShiftedUnexpandedPC_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .nextUnexpandedPC i -
        HonestWitness.shiftedColumn 0 (witness.virtual .unexpandedPC) i = 0

private def nextPCEqShiftedPC_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .nextPC i -
        HonestWitness.shiftedColumn 0 (witness.virtual .pc) i = 0

private def nextIsVirtualEqShiftedVirtualInstruction_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .nextIsVirtual i -
        HonestWitness.shiftedColumn 0
          (witness.opFlag .virtualInstruction) i = 0

private def nextIsFirstInSequenceEqShiftedFirstInSequence_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .nextIsFirstInSequence i -
        HonestWitness.shiftedColumn 0
          (witness.opFlag .isFirstInSequence) i = 0

private def nextIsNoopEqShiftedNoop_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.virtual .nextIsNoop i -
        HonestWitness.shiftedColumn 1
          (witness.instructionFlag .isNoop) i = 0

private def leftInstructionInputEqSelectedOperands_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.leftInstructionInput i -
        (witness.instructionFlag .leftOperandIsRs1Value i *
            witness.rs1Value i +
          witness.instructionFlag .leftOperandIsPC i *
            witness.virtual .unexpandedPC i) = 0

private def rightInstructionInputEqSelectedOperands_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.rightInstructionInput i -
        (witness.instructionFlag .rightOperandIsRs2Value i *
            witness.rs2Value i +
          witness.instructionFlag .rightOperandIsImm i *
            witness.virtual .imm i) = 0

private def rs1ValueEqSelectedRegistersVal_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.rs1Value i -
        ∑ address : RegisterAddress,
          witness.rs1Ra address i * witness.registersVal address i = 0

private def rs2ValueEqSelectedRegistersVal_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.rs2Value i -
        ∑ address : RegisterAddress,
          witness.rs2Ra address i * witness.registersVal address i = 0

private def rdWriteValueEqSelectedRegistersValPlusIncrement_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.rdWriteValue i -
        ∑ address : RegisterAddress,
          witness.rdWa address i *
            (witness.registersVal address i + witness.rdInc i) = 0

private def ramValEqInitialValuePlusPriorIncrements_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  ∀ (address : Fin params.ramK) (i : Fin params.traceLength),
    witness.ramVal address i -
        (witness.initialRamValue publicInputs address +
          HonestWitness.strictPrefixSum
            (fun j => witness.ramRa address j * witness.ramInc j) i) = 0

private def ramValFinalEqInitialValuePlusAllIncrements_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  ∀ address : Fin params.ramK,
    witness.ramValFinal address -
        (witness.initialRamValue publicInputs address +
          ∑ i : Fin params.traceLength,
            witness.ramRa address i * witness.ramInc i) = 0

private def lookupOutputEqInstructionReadRaf_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.lookupOutput i -
        ∑ address : InstructionLookupAddress,
          witness.instructionRaProduct address i *
            ∑ table : JoltLookupTable,
              HonestWitness.fieldFromU64 (F := F)
                  (JoltLookupTable.materializeEntry table address) *
                witness.lookupTableFlag table i = 0

private def leftLookupOperandEqInstructionReadRaf_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.leftLookupOperand i -
        ∑ address : InstructionLookupAddress,
          witness.instructionRaProduct address i *
            ((HonestWitness.fieldFromU64 (F := F) address.leftOperand) *
              (1 - witness.instructionRafFlag i)) = 0

private def rightLookupOperandEqInstructionReadRaf_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.rightLookupOperand i -
        ∑ address : InstructionLookupAddress,
          witness.instructionRaProduct address i *
            (HonestWitness.fieldFromU64 (F := F) address.rightOperand +
              witness.instructionRafFlag i *
                ((address.val : F) -
                  HonestWitness.fieldFromU64 (F := F)
                    address.rightOperand)) = 0

private def registersValEqPriorWrites_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (address : RegisterAddress) (i : Fin params.traceLength),
    witness.registersVal address i -
        HonestWitness.strictPrefixSum
          (fun j => witness.rdWa address j * witness.rdInc j) i = 0

private def instructionRaBooleanity_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (chunk : Fin params.instructionCommittedRaCount)
      (address : Fin params.committedChunkSize)
      (i : Fin params.traceLength),
    witness.instructionRa chunk address i *
          witness.instructionRa chunk address i -
        witness.instructionRa chunk address i = 0

private def bytecodeRaBooleanity_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (chunk : Fin params.bytecodeCommittedRaCount)
      (address : Fin params.committedChunkSize)
      (i : Fin params.traceLength),
    witness.bytecodeRa chunk address i *
          witness.bytecodeRa chunk address i -
        witness.bytecodeRa chunk address i = 0

private def ramRaBooleanity_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (chunk : Fin params.ramCommittedRaCount)
      (address : Fin params.committedChunkSize)
      (i : Fin params.traceLength),
    witness.ramCommittedRa chunk address i *
          witness.ramCommittedRa chunk address i -
        witness.ramCommittedRa chunk address i = 0

private def instructionRaVirtualization_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (virtualChunk : Fin params.instructionVirtualRaCount)
      (address : Fin params.lookupVirtualChunkSize)
      (i : Fin params.traceLength),
    witness.instructionVirtualRa virtualChunk address i -
        witness.instructionCommittedRaProduct virtualChunk address i = 0

private def ramRaVirtualization_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ (address : Fin params.ramK) (i : Fin params.traceLength),
    witness.ramRa address i -
        witness.ramCommittedRaProduct address i = 0

private def ramHammingWeightBooleanity_satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) : Prop :=
  ∀ i : Fin params.traceLength,
    witness.ramHammingWeight i * witness.ramHammingWeight i -
        witness.ramHammingWeight i = 0

def JoltConstraint.Satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (constraint : JoltConstraint)
    (publicInputs : JoltPublicInputs params)
    (witness : JoltWitness params F) : Prop :=
  match constraint with
  | .ramAddrEqRs1PlusImmIfLoadStore =>
      ramAddrEqRs1PlusImmIfLoadStore_satisfied witness
  | .ramAddrEqZeroIfNotLoadStore => ramAddrEqZeroIfNotLoadStore_satisfied witness
  | .ramReadEqRamWriteIfLoad => ramReadEqRamWriteIfLoad_satisfied witness
  | .ramReadEqRdWriteIfLoad => ramReadEqRdWriteIfLoad_satisfied witness
  | .rs2EqRamWriteIfStore => rs2EqRamWriteIfStore_satisfied witness
  | .leftLookupZeroUnlessAddSubMul => leftLookupZeroUnlessAddSubMul_satisfied witness
  | .leftLookupEqLeftInputOtherwise =>
      leftLookupEqLeftInputOtherwise_satisfied witness
  | .rightLookupAdd => rightLookupAdd_satisfied witness
  | .rightLookupSub => rightLookupSub_satisfied witness
  | .rightLookupEqProductIfMul => rightLookupEqProductIfMul_satisfied witness
  | .rightLookupEqRightInputOtherwise =>
      rightLookupEqRightInputOtherwise_satisfied witness
  | .assertLookupOne => assertLookupOne_satisfied witness
  | .rdWriteEqLookupIfWriteLookupToRD =>
      rdWriteEqLookupIfWriteLookupToRD_satisfied witness
  | .rdWriteEqPCPlusConstIfWritePCToRD =>
      rdWriteEqPCPlusConstIfWritePCToRD_satisfied witness
  | .nextUnexpandedPCEqLookupIfShouldJump =>
      nextUnexpandedPCEqLookupIfShouldJump_satisfied witness
  | .nextUnexpandedPCEqPCPlusImmIfShouldBranch =>
      nextUnexpandedPCEqPCPlusImmIfShouldBranch_satisfied witness
  | .nextUnexpandedPCUpdateOtherwise =>
      nextUnexpandedPCUpdateOtherwise_satisfied witness
  | .nextPCEqPCPlusOneIfInline => nextPCEqPCPlusOneIfInline_satisfied witness
  | .mustStartSequenceFromBeginning => mustStartSequenceFromBeginning_satisfied witness
  | .productEqLeftInputMulRightInput => productEqLeftInputMulRightInput_satisfied witness
  | .shouldBranchEqLookupOutputMulBranch =>
      shouldBranchEqLookupOutputMulBranch_satisfied witness
  | .shouldJumpEqJumpMulNotNextIsNoop =>
      shouldJumpEqJumpMulNotNextIsNoop_satisfied witness
  | .ramReadValueEqSelectedRamValue =>
      ramReadValueEqSelectedRamValue_satisfied witness
  | .ramWriteValueEqSelectedRamValuePlusIncrement =>
      ramWriteValueEqSelectedRamValuePlusIncrement_satisfied witness
  | .ramAddressEqSelectedRamAddress =>
      ramAddressEqSelectedRamAddress_satisfied publicInputs witness
  | .ramFinalValueEqPublicIo =>
      ramFinalValueEqPublicIo_satisfied publicInputs witness
  | .nextUnexpandedPCEqShiftedUnexpandedPC =>
      nextUnexpandedPCEqShiftedUnexpandedPC_satisfied witness
  | .nextPCEqShiftedPC => nextPCEqShiftedPC_satisfied witness
  | .nextIsVirtualEqShiftedVirtualInstruction =>
      nextIsVirtualEqShiftedVirtualInstruction_satisfied witness
  | .nextIsFirstInSequenceEqShiftedFirstInSequence =>
      nextIsFirstInSequenceEqShiftedFirstInSequence_satisfied witness
  | .nextIsNoopEqShiftedNoop => nextIsNoopEqShiftedNoop_satisfied witness
  | .leftInstructionInputEqSelectedOperands =>
      leftInstructionInputEqSelectedOperands_satisfied witness
  | .rightInstructionInputEqSelectedOperands =>
      rightInstructionInputEqSelectedOperands_satisfied witness
  | .rs1ValueEqSelectedRegistersVal =>
      rs1ValueEqSelectedRegistersVal_satisfied witness
  | .rs2ValueEqSelectedRegistersVal =>
      rs2ValueEqSelectedRegistersVal_satisfied witness
  | .rdWriteValueEqSelectedRegistersValPlusIncrement =>
      rdWriteValueEqSelectedRegistersValPlusIncrement_satisfied witness
  | .ramValEqInitialValuePlusPriorIncrements =>
      ramValEqInitialValuePlusPriorIncrements_satisfied publicInputs witness
  | .ramValFinalEqInitialValuePlusAllIncrements =>
      ramValFinalEqInitialValuePlusAllIncrements_satisfied publicInputs witness
  | .lookupOutputEqInstructionReadRaf =>
      lookupOutputEqInstructionReadRaf_satisfied witness
  | .leftLookupOperandEqInstructionReadRaf =>
      leftLookupOperandEqInstructionReadRaf_satisfied witness
  | .rightLookupOperandEqInstructionReadRaf =>
      rightLookupOperandEqInstructionReadRaf_satisfied witness
  | .registersValEqPriorWrites =>
      registersValEqPriorWrites_satisfied witness
  | .instructionRaBooleanity =>
      instructionRaBooleanity_satisfied witness
  | .bytecodeRaBooleanity =>
      bytecodeRaBooleanity_satisfied witness
  | .ramRaBooleanity =>
      ramRaBooleanity_satisfied witness
  | .instructionRaVirtualization =>
      instructionRaVirtualization_satisfied witness
  | .ramRaVirtualization =>
      ramRaVirtualization_satisfied witness
  | .ramHammingWeightBooleanity =>
      ramHammingWeightBooleanity_satisfied witness

end JoltConstraints
