import JoltConstraints.witness

namespace JoltConstraints

universe u

-- NOTE: We are assuming that the bytecode is fixed and public for now.
-- Constraints for Jolt's committed-program mode are not modelled here.

/-!
# Jolt RV64 R1CS constraints

Each constructor names one of the 22 constraints in Jolt's full RV64 trace
R1CS. The first 19 are conditional equalities of the form
`guard * (left - right) = 0`; the final three define product columns.
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
  | productEqLeftInputMulRightInput
  | shouldBranchEqLookupOutputMulBranch
  | shouldJumpEqJumpMulNotNextIsNoop
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

def JoltConstraint.Satisfied
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (constraint : JoltConstraint) (witness : JoltWitness params F) : Prop :=
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

end JoltConstraints
