import JoltConstraints.basic

namespace JoltConstraints

universe u

open scoped BigOperators

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

namespace HonestWitness

/-- Index of the next trace row, with no wrap at the final row. -/
def nextTraceIndex {T : Nat} (i : Fin T) : Option (Fin T) :=
  if hasNext : i.val + 1 < T then some ⟨i.val + 1, hasNext⟩ else none

/-- One-step, non-wrapping shift of a finite trace column.  This is the
Boolean-hypercube meaning of Rust's `EqPlusOnePolynomial`. -/
def shiftedColumn {T : Nat} {α : Type u}
    (terminal : α) (column : Column T α) (i : Fin T) : α :=
  match nextTraceIndex i with
  | some next => column next
  | none => terminal

/-- Sum of the entries strictly before row `i`.  This is the finite-array
counterpart of Rust's `LtPolynomial` evaluation on a Boolean cycle. -/
def strictPrefixSum {T : Nat} {α : Type u} [AddCommMonoid α]
    (column : Column T α) (i : Fin T) : α :=
  ∑ j : Fin i.val,
    column ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

end HonestWitness

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
  deriving DecidableEq, Fintype, Repr

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

/-! These are exactly the base-mode polynomial families materialized by
Rust's `TraceBackedJoltVmWitness`.  Rust enum variants used only for derived
claims, committed-program mode, or lattice mode intentionally do not appear. -/

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
  | .pc
  | .unexpandedPC
  | .nextPC
  | .nextUnexpandedPC
  | .nextIsNoop
  | .nextIsVirtual
  | .nextIsFirstInSequence
  | .leftLookupOperand
  | .rightLookupOperand
  | .leftInstructionInput
  | .rightInstructionInput
  | .product
  | .shouldJump
  | .shouldBranch
  | .imm
  | .rs1Value
  | .rs2Value
  | .rdWriteValue
  | .lookupOutput
  | .instructionRafFlag
  | .ramAddress
  | .ramReadValue
  | .ramWriteValue
  | .ramHammingWeight
  | .opFlag _
  | .instructionFlag _
  | .lookupTableFlag _ => TraceColumn params F

structure JoltWitness (params : JoltWitnessParams) (F : Type u) where
  committed : (polynomial : JoltCommittedPolynomial params) →
    polynomial.EvaluationsType F
  virtual : (polynomial : JoltVirtualPolynomial params) →
    polynomial.EvaluationsType F

def JoltWitness.rdInc {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.committed .rdInc

def JoltWitness.ramInc {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.committed .ramInc

def JoltWitness.instructionRa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.instructionCommittedRaCount) :
    CommittedRaColumns params F :=
  witness.committed (.instructionRa chunk)

def JoltWitness.bytecodeRa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.bytecodeCommittedRaCount) :
    CommittedRaColumns params F :=
  witness.committed (.bytecodeRa chunk)

def JoltWitness.ramCommittedRa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.ramCommittedRaCount) :
    CommittedRaColumns params F :=
  witness.committed (.ramRa chunk)

/-- Product of every committed bytecode-RA digit at one complete bytecode
address. This is shared infrastructure; it does not itself impose a public
bytecode-table constraint. -/
def JoltWitness.bytecodeRaProduct
    {params : JoltWitnessParams} {F : Type u} [CommMonoid F]
    (witness : JoltWitness params F)
    (address : Fin params.bytecodeK) (i : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.bytecodeCommittedRaCount,
    witness.bytecodeRa chunk
      ((params.bytecodeCommittedSelector chunk).chunk address.val) i

/-- Read one public bytecode table column with the full address selector
reconstructed from Rust's committed `D` read-address digits. -/
def JoltWitness.bytecodeRead
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (witness : JoltWitness params F) (values : Column params.bytecodeK F)
    (i : Fin params.traceLength) : F :=
  ∑ address : Fin params.bytecodeK,
    witness.bytecodeRaProduct address i * values address

/-- Product of every committed RAM-RA digit at one complete remapped RAM
address. -/
def JoltWitness.ramCommittedRaProduct
    {params : JoltWitnessParams} {F : Type u} [CommMonoid F]
    (witness : JoltWitness params F)
    (address : Fin params.ramK) (i : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.ramCommittedRaCount,
    witness.ramCommittedRa chunk
      ((params.ramCommittedSelector chunk).chunk address.val) i

def JoltWitness.trustedAdvice {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (included : params.includeTrustedAdvice = true) :
    Column params.trustedAdviceLength F :=
  witness.committed (.trustedAdvice included)

def JoltWitness.untrustedAdvice {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (included : params.includeUntrustedAdvice = true) :
    Column params.untrustedAdviceLength F :=
  witness.committed (.untrustedAdvice included)

/-- Total field-valued read from the optional trusted-advice commitment. -/
def JoltWitness.trustedAdviceWord
    {params : JoltWitnessParams} {F : Type u} [Zero F]
    (witness : JoltWitness params F) (index : Nat) : F :=
  if included : params.includeTrustedAdvice = true then
    if inBounds : index < params.trustedAdviceLength then
      witness.trustedAdvice included ⟨index, inBounds⟩
    else
      0
  else
    0

/-- Total field-valued read from the optional untrusted-advice commitment. -/
def JoltWitness.untrustedAdviceWord
    {params : JoltWitnessParams} {F : Type u} [Zero F]
    (witness : JoltWitness params F) (index : Nat) : F :=
  if included : params.includeUntrustedAdvice = true then
    if inBounds : index < params.untrustedAdviceLength then
      witness.untrustedAdvice included ⟨index, inBounds⟩
    else
      0
  else
    0

/-- Trusted-advice contribution at one remapped RAM address. -/
def JoltWitness.trustedAdviceAt?
    {params : JoltWitnessParams} {F : Type u} [Zero F]
    (publicInputs : JoltPublicInputs params) (witness : JoltWitness params F)
    (address : Fin params.ramK) : Option F :=
  if params.includeTrustedAdvice then
    (publicInputs.trustedAdviceRegion.index? address).map
      (fun index => witness.trustedAdviceWord index.val)
  else
    none

/-- Untrusted-advice contribution at one remapped RAM address. -/
def JoltWitness.untrustedAdviceAt?
    {params : JoltWitnessParams} {F : Type u} [Zero F]
    (publicInputs : JoltPublicInputs params) (witness : JoltWitness params F)
    (address : Fin params.ramK) : Option F :=
  if params.includeUntrustedAdvice then
    (publicInputs.untrustedAdviceRegion.index? address).map
      (fun index => witness.untrustedAdviceWord index.val)
  else
    none

/-- Full initial RAM value reconstructed from public memory and the two
optional committed advice streams, in Rust's overlay order. -/
def JoltWitness.initialRamValue
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (publicInputs : JoltPublicInputs params) (witness : JoltWitness params F)
    (address : Fin params.ramK) : F :=
  match witness.untrustedAdviceAt? publicInputs address with
  | some value => value
  | none =>
      match witness.trustedAdviceAt? publicInputs address with
      | some value => value
      | none => ((publicInputs.publicInitialRam address).toNat : F)

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

def JoltWitness.instructionVirtualRa
    {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F)
    (chunk : Fin params.instructionVirtualRaCount) :
    InstructionVirtualRaColumns params F :=
  witness.virtual (.instructionRa chunk)

/-- Product of the contiguous committed instruction-RA chunks represented by
one virtual instruction-RA chunk. The checked chunk map can fail only for raw,
invalid parameters; production-valid dimensions prove every factor present. -/
def JoltWitness.instructionCommittedRaProduct
    {params : JoltWitnessParams} {F : Type u} [CommMonoidWithZero F]
    (witness : JoltWitness params F)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (address : Fin params.lookupVirtualChunkSize)
    (i : Fin params.traceLength) : F :=
  ∏ localChunk : Fin params.instructionCommittedRaPerVirtual,
    match params.instructionCommittedChunk? virtualChunk localChunk with
    | some committedChunk =>
        witness.instructionRa committedChunk
          ((params.instructionCommittedLocalSelector localChunk).chunk
            address.val) i
    | none => 0

/-- Product of the virtual instruction read-address chunks at one complete
128-bit lookup address and trace row. -/
def JoltWitness.instructionRaProduct
    {params : JoltWitnessParams} {F : Type u} [CommMonoid F]
    (witness : JoltWitness params F)
    (address : InstructionLookupAddress) (i : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.instructionVirtualRaCount,
    witness.instructionVirtualRa chunk
      ((params.instructionVirtualSelector chunk).chunk address.val) i

def JoltWitness.registersVal {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RegisterColumns params F :=
  witness.virtual .registersVal

def JoltWitness.ramRa {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RamReadWriteColumns params F :=
  witness.virtual .ramRa

def JoltWitness.ramVal {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RamReadWriteColumns params F :=
  witness.virtual .ramVal

def JoltWitness.ramValFinal {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : RamFinalColumn params F :=
  witness.virtual .ramValFinal

def JoltWitness.ramAddress {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .ramAddress

def JoltWitness.ramReadValue {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .ramReadValue

def JoltWitness.ramWriteValue {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .ramWriteValue

def JoltWitness.ramHammingWeight
    {params : JoltWitnessParams} {F : Type u}
    (witness : JoltWitness params F) : TraceColumn params F :=
  witness.virtual .ramHammingWeight

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
