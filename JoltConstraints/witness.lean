import JoltConstraints.basic

namespace JoltConstraints

universe u

abbrev RegisterAddressBits : Nat := 7

abbrev RegisterAddressCount : Nat := 2 ^ RegisterAddressBits

abbrev RegisterAddress : Type := Fin RegisterAddressCount

abbrev InstructionLookupAddressBits : Nat := 2 * Xlen

abbrev InstructionLookupAddressCount : Nat :=
  2 ^ InstructionLookupAddressBits

abbrev InstructionLookupAddress : Type := Fin InstructionLookupAddressCount

abbrev TraceColumn (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column params.traceLength F

abbrev RegisterColumns (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column RegisterAddressCount (TraceColumn params F)

abbrev RamReadWriteColumns (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column params.ramK (TraceColumn params F)

abbrev RamFinalColumn (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column params.ramK F

abbrev CommittedRaColumns (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column params.committedChunkSize (TraceColumn params F)

abbrev InstructionVirtualRaColumns
    (params : JoltWitnessParams) (F : Type u) : Type u :=
  Column params.lookupVirtualChunkSize (TraceColumn params F)

inductive JoltLookupTable where
  | RangeCheck
  | RangeCheckAligned
  | AND
  | ANDN
  | OR
  | XOR
  | Equal
  | SignedGreaterThanEqual
  | UnsignedGreaterThanEqual
  | NotEqual
  | SignedLessThan
  | UnsignedLessThan
  | SignMask
  | UpperWord
  | UnsignedLessThanEqual
  | ValidUnsignedRemainder
  | ValidDiv0
  | HalfwordAlignment
  | WordAlignment
  | LowerHalfWord
  | SignExtendHalfWord
  | Pow2
  | Pow2W
  | ShiftRightBitmask
  | VirtualRev8W
  | VirtualSRL
  | VirtualSRA
  | VirtualROTR
  | VirtualROTRW
  | VirtualChangeDivisor
  | VirtualChangeDivisorW
  | MulUNoOverflow
  | VirtualXORROT32
  | VirtualXORROT24
  | VirtualXORROT16
  | VirtualXORROT63
  | VirtualXORROTW16
  | VirtualXORROTW12
  | VirtualXORROTW8
  | VirtualXORROTW7
  deriving DecidableEq, Repr

inductive JoltCircuitFlag where
  | addOperands
  | subtractOperands
  | multiplyOperands
  | load
  | store
  | jump
  | writeLookupOutputToRD
  | virtualInstruction
  | assert
  | doNotUpdateUnexpandedPC
  | advice
  | isCompressed
  | isFirstInSequence
  | isLastInSequence
  deriving DecidableEq, Repr

inductive JoltInstructionFlag where
  | leftOperandIsPC
  | rightOperandIsImm
  | leftOperandIsRs1Value
  | rightOperandIsRs2Value
  | branch
  | isNoop
  deriving DecidableEq, Repr

inductive JoltCommittedPolynomial (params : JoltWitnessParams) where
  | rdInc
  | ramInc
  | instructionRa (chunk : Fin params.instructionCommittedRaCount)
  | bytecodeRa (chunk : Fin params.bytecodeCommittedRaCount)
  | ramRa (chunk : Fin params.ramCommittedRaCount)
  | trustedAdvice (included : params.includeTrustedAdvice = true)
  | untrustedAdvice (included : params.includeUntrustedAdvice = true)
  deriving DecidableEq, Repr

inductive JoltVirtualPolynomial (params : JoltWitnessParams) where
  | pc
  | unexpandedPC
  | nextPC
  | nextUnexpandedPC
  | nextIsNoop
  | nextIsVirtual
  | nextIsFirstInSequence
  | leftLookupOperand
  | rightLookupOperand
  | leftInstructionInput
  | rightInstructionInput
  | product
  | shouldJump
  | shouldBranch
  | imm
  | rs1Value
  | rs2Value
  | rdWriteValue
  | rs1Ra
  | rs2Ra
  | rdWa
  | lookupOutput
  | instructionRafFlag
  | instructionRa (chunk : Fin params.instructionVirtualRaCount)
  | registersVal
  | ramAddress
  | ramRa
  | ramReadValue
  | ramWriteValue
  | ramVal
  | ramValFinal
  | ramHammingWeight
  | opFlag (flag : JoltCircuitFlag)
  | instructionFlag (flag : JoltInstructionFlag)
  | lookupTableFlag (table : JoltLookupTable)
  deriving DecidableEq, Repr

def JoltCommittedPolynomial.EvaluationsType
    {params : JoltWitnessParams}
    (polynomial : JoltCommittedPolynomial params)
    (F : Type u) : Type u :=
  match polynomial with
  | .rdInc
  | .ramInc => TraceColumn params F
  | .instructionRa _
  | .bytecodeRa _
  | .ramRa _ => CommittedRaColumns params F
  | .trustedAdvice _ => Column params.trustedAdviceLength F
  | .untrustedAdvice _ => Column params.untrustedAdviceLength F

def JoltVirtualPolynomial.EvaluationsType
    {params : JoltWitnessParams}
    (polynomial : JoltVirtualPolynomial params)
    (F : Type u) : Type u :=
  match polynomial with
  | .rs1Ra
  | .rs2Ra
  | .rdWa
  | .registersVal => RegisterColumns params F
  | .ramRa
  | .ramVal => RamReadWriteColumns params F
  | .ramValFinal => RamFinalColumn params F
  | .instructionRa _ => InstructionVirtualRaColumns params F
  | _ => TraceColumn params F

structure JoltWitness (params : JoltWitnessParams) (F : Type u) where
  committed : (polynomial : JoltCommittedPolynomial params) →
    polynomial.EvaluationsType F
  virtual : (polynomial : JoltVirtualPolynomial params) →
    polynomial.EvaluationsType F

def JoltWitness.rdInc {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.committed .rdInc

def JoltWitness.instructionRa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.instructionCommittedRaCount) :
    CommittedRaColumns params F :=
  witness.committed (.instructionRa chunk)

def JoltWitness.leftLookupOperand {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .leftLookupOperand

def JoltWitness.rightLookupOperand {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .rightLookupOperand

def JoltWitness.leftInstructionInput {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .leftInstructionInput

def JoltWitness.rightInstructionInput {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .rightInstructionInput

def JoltWitness.rs1Value {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .rs1Value

def JoltWitness.rs2Value {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .rs2Value

def JoltWitness.rdWriteValue {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .rdWriteValue

def JoltWitness.lookupOutput {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .lookupOutput

def JoltWitness.instructionRafFlag {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .instructionRafFlag

def JoltWitness.rs1Ra {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RegisterColumns params F :=
  witness.virtual .rs1Ra

def JoltWitness.rs2Ra {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RegisterColumns params F :=
  witness.virtual .rs2Ra

def JoltWitness.rdWa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RegisterColumns params F :=
  witness.virtual .rdWa

def JoltWitness.opFlag {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) (flag : JoltCircuitFlag) :
    TraceColumn params F :=
  witness.virtual (.opFlag flag)

def JoltWitness.instructionFlag {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) (flag : JoltInstructionFlag) :
    TraceColumn params F :=
  witness.virtual (.instructionFlag flag)

def JoltWitness.lookupTableFlag {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) (table : JoltLookupTable) :
    TraceColumn params F :=
  witness.virtual (.lookupTableFlag table)

def JoltWitness.writeLookupOutputToRD
    {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.opFlag .writeLookupOutputToRD

def JoltWitness.AND_FLAG {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.lookupTableFlag .AND

def JoltWitness.RD_val {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.rdWriteValue

def JoltWitness.ra {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.instructionCommittedRaCount) :
    CommittedRaColumns params F :=
  witness.instructionRa chunk

end JoltConstraints
