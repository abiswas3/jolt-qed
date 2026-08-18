import JoltConstraints.witness

namespace JoltConstraints

universe u

open scoped BigOperators

-- NOTE: We are assuming that the bytecode is fixed and public for now.
-- Constraints for Jolt's committed-program mode are not modelled here.

/-!
# Jolt witness constraints

Each constructor names one unbatched identity tested by a Jolt sumcheck. The
first 19 constructors are the equality-conditional RV64 constraints tested by
Stage 1's `SpartanOuter`. The next three are the product constraints tested by
Stage 2's `SpartanProductVirtualization`, and the final four are the RAM witness
relations tested in Stage 2. Claim reductions and sumcheck round-splitting
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

end JoltConstraints
