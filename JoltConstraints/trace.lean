import JoltConstraints.witness

namespace JoltConstraints

open Sail PreSail LeanRV64D.Functions

universe u

namespace HonestWitness

abbrev U64 := BitVec Xlen

abbrev U128 := BitVec InstructionLookupAddressBits

def fieldFromU64 {F : Type u} [Field F] (value : U64) : F :=
  (value.toNat : F)

def fieldFromU128 {F : Type u} [Field F] (value : U128) : F :=
  (value.toNat : F)

def fieldFromI128 {F : Type u} [Field F] (value : U128) : F :=
  (value.toInt : F)

def fieldFromInt {F : Type u} [Field F] (value : Int) : F :=
  (value : F)

def destinationSource : JoltISA.Dst → JoltISA.Src
  | .vreg register => .vreg register
  | .xreg register => .xreg register

def sourceAddress : JoltISA.Src → RegisterAddress
  | .vreg register => register.toFin
  | .xreg (regidx.Regidx register) =>
      (BitVec.ofNat RegisterAddressBits register.toNat).toFin

def destinationAddress (destination : JoltISA.Dst) : RegisterAddress :=
  sourceAddress (destinationSource destination)

noncomputable def sourceValue
    (state : SailJoltState) (source : JoltISA.Src) : BitVec Xlen :=
  match (JoltISA.readSrc source).run state with
  | .ok value _ => value
  | .error _ _ => 0

noncomputable def destinationValue
    (state : SailJoltState) (destination : JoltISA.Dst) : BitVec Xlen :=
  sourceValue state (destinationSource destination)

def destination : JoltISA.Instr → Option JoltISA.Dst
  | .ADDI dst _ _
  | .ANDI dst _ _
  | .ORI dst _ _
  | .XORI dst _ _
  | .SLTI dst _ _
  | .SLTIU dst _ _
  | .LUI dst _
  | .AUIPC dst _
  | .JAL dst _
  | .JALR dst _ _
  | .ADD dst _ _
  | .SUB dst _ _
  | .MUL dst _ _
  | .MULHU dst _ _
  | .ANDN dst _ _
  | .VirtualMULI dst _ _
  | .VirtualPow2 dst _
  | .VirtualPow2W dst _
  | .VirtualPow2I dst _
  | .VirtualPow2IW dst _
  | .VirtualShiftRightBitmask dst _
  | .VirtualShiftRightBitmaskI dst _
  | .VirtualSRLI dst _ _
  | .VirtualSRAI dst _ _
  | .VirtualSRL dst _ _
  | .VirtualSRA dst _ _
  | .VirtualROTRI dst _ _
  | .VirtualROTRIW dst _ _
  | .VirtualRev8W dst _
  | .VirtualXORROT32 dst _ _
  | .VirtualXORROT24 dst _ _
  | .VirtualXORROT16 dst _ _
  | .VirtualXORROT63 dst _ _
  | .VirtualXORROTW16 dst _ _
  | .VirtualXORROTW12 dst _ _
  | .VirtualXORROTW8 dst _ _
  | .VirtualXORROTW7 dst _ _
  | .OR dst _ _
  | .XOR dst _ _
  | .AND dst _ _
  | .SLT dst _ _
  | .SLTU dst _ _
  | .VirtualSignExtendWord dst _
  | .VirtualZeroExtendWord dst _
  | .VirtualMovsign dst _
  | .LD _ dst _ _
  | .VirtualAdvice dst _
  | .VirtualAdviceLoad dst _
  | .VirtualAdviceLen dst _
  | .VirtualChangeDivisor dst _ _
  | .VirtualChangeDivisorW dst _ _ => some dst
  | _ => none

def firstSource : JoltISA.Instr → Option JoltISA.Src
  | .ADDI _ source _
  | .ANDI _ source _
  | .ORI _ source _
  | .XORI _ source _
  | .SLTI _ source _
  | .SLTIU _ source _
  | .JALR _ source _
  | .VirtualMULI _ source _
  | .VirtualPow2 _ source
  | .VirtualPow2W _ source
  | .VirtualShiftRightBitmask _ source
  | .VirtualSRLI _ source _
  | .VirtualSRAI _ source _
  | .VirtualROTRI _ source _
  | .VirtualROTRIW _ source _
  | .VirtualRev8W _ source
  | .VirtualSignExtendWord _ source
  | .VirtualZeroExtendWord _ source
  | .VirtualMovsign _ source
  | .LD _ _ source _ => some source

  | .BEQ lhs _ _
  | .BNE lhs _ _
  | .BLT lhs _ _
  | .BGE lhs _ _
  | .BLTU lhs _ _
  | .BGEU lhs _ _
  | .ADD _ lhs _
  | .SUB _ lhs _
  | .MUL _ lhs _
  | .MULHU _ lhs _
  | .ANDN _ lhs _
  | .VirtualSRL _ lhs _
  | .VirtualSRA _ lhs _
  | .VirtualXORROT32 _ lhs _
  | .VirtualXORROT24 _ lhs _
  | .VirtualXORROT16 _ lhs _
  | .VirtualXORROT63 _ lhs _
  | .VirtualXORROTW16 _ lhs _
  | .VirtualXORROTW12 _ lhs _
  | .VirtualXORROTW8 _ lhs _
  | .VirtualXORROTW7 _ lhs _
  | .OR _ lhs _
  | .XOR _ lhs _
  | .AND _ lhs _
  | .SLT _ lhs _
  | .SLTU _ lhs _
  | .SD lhs _ _
  | .VirtualAssertEQ lhs _ _
  | .VirtualAssertValidDiv0 lhs _
  | .VirtualChangeDivisor _ lhs _
  | .VirtualChangeDivisorW _ lhs _
  | .VirtualAssertValidUnsignedRemainder lhs _
  | .VirtualAssertMulUNoOverflow lhs _
  | .VirtualAssertLTE lhs _ => some lhs

  | .VirtualAssertHalfwordAlignment base _ _
  | .VirtualAssertWordAlignment base _ _ => some (.xreg base)
  | _ => none

def secondSource : JoltISA.Instr → Option JoltISA.Src
  | .BEQ _ rhs _
  | .BNE _ rhs _
  | .BLT _ rhs _
  | .BGE _ rhs _
  | .BLTU _ rhs _
  | .BGEU _ rhs _
  | .ADD _ _ rhs
  | .SUB _ _ rhs
  | .MUL _ _ rhs
  | .MULHU _ _ rhs
  | .ANDN _ _ rhs
  | .VirtualSRL _ _ rhs
  | .VirtualSRA _ _ rhs
  | .VirtualXORROT32 _ _ rhs
  | .VirtualXORROT24 _ _ rhs
  | .VirtualXORROT16 _ _ rhs
  | .VirtualXORROT63 _ _ rhs
  | .VirtualXORROTW16 _ _ rhs
  | .VirtualXORROTW12 _ _ rhs
  | .VirtualXORROTW8 _ _ rhs
  | .VirtualXORROTW7 _ _ rhs
  | .OR _ _ rhs
  | .XOR _ _ rhs
  | .AND _ _ rhs
  | .SLT _ _ rhs
  | .SLTU _ _ rhs
  | .SD _ rhs _
  | .VirtualAssertEQ _ rhs _
  | .VirtualAssertValidDiv0 _ rhs
  | .VirtualChangeDivisor _ _ rhs
  | .VirtualChangeDivisorW _ _ rhs
  | .VirtualAssertValidUnsignedRemainder _ rhs
  | .VirtualAssertMulUNoOverflow _ rhs
  | .VirtualAssertLTE _ rhs =>
      some rhs
  | _ => none

def lookupFirstSource (instruction : JoltISA.Instr) : Option JoltISA.Src :=
  match instruction with
  | .LD _ _ _ _ | .SD _ _ _ => none
  | _ => firstSource instruction

def lookupSecondSource (instruction : JoltISA.Instr) : Option JoltISA.Src :=
  match instruction with
  | .SD _ _ _ => none
  | _ => secondSource instruction

def instructionImmediate : JoltISA.Instr → Int
  | .ADDI _ _ immediate
  | .ANDI _ _ immediate
  | .ORI _ _ immediate
  | .XORI _ _ immediate
  | .SLTI _ _ immediate
  | .SLTIU _ _ immediate
  | .JALR _ _ immediate
  | .LD _ _ _ immediate
  | .SD _ _ immediate =>
      (sign_extend (m := Xlen) immediate).toInt
  | .LUI _ immediate => immediate.toInt
  | .AUIPC _ immediate =>
      (sign_extend (m := Xlen) (immediate +++ (0 : BitVec 12))).toInt
  | .JAL _ immediate => (sign_extend (m := Xlen) immediate).toInt
  | .BEQ _ _ immediate
  | .BNE _ _ immediate
  | .BLT _ _ immediate
  | .BGE _ _ immediate
  | .BLTU _ _ immediate
  | .BGEU _ _ immediate
  | .VirtualAssertEQ _ _ immediate =>
      (sign_extend (m := Xlen) immediate).toInt
  | .VirtualMULI _ _ immediate => immediate.toNat
  | .VirtualPow2I _ immediate
  | .VirtualPow2IW _ immediate
  | .VirtualShiftRightBitmaskI _ immediate
  | .VirtualSRLI _ _ immediate
  | .VirtualSRAI _ _ immediate
  | .VirtualROTRI _ _ immediate
  | .VirtualROTRIW _ _ immediate => immediate
  | .VirtualMovsign _ _ => 0
  | .VirtualAssertHalfwordAlignment _ immediate _
  | .VirtualAssertWordAlignment _ immediate _ =>
      immediate.toInt
  | _ => 0

def rightOperandIsImmediate : JoltISA.Instr → Bool
  | .ADDI _ _ _
  | .ANDI _ _ _
  | .ORI _ _ _
  | .XORI _ _ _
  | .SLTI _ _ _
  | .SLTIU _ _ _
  | .LUI _ _
  | .AUIPC _ _
  | .JAL _ _
  | .JALR _ _ _
  | .VirtualMULI _ _ _
  | .VirtualPow2I _ _
  | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmaskI _ _
  | .VirtualSRLI _ _ _
  | .VirtualSRAI _ _ _
  | .VirtualROTRI _ _ _
  | .VirtualROTRIW _ _ _
  | .VirtualMovsign _ _
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _ => true
  | _ => false

def signedInstructionImmediate : JoltISA.Instr → Bool
  | .AUIPC _ _
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _ => true
  | _ => false

def lowImmediate (instruction : JoltISA.Instr) : Option U128 :=
  if rightOperandIsImmediate instruction then
    if signedInstructionImmediate instruction then
      some (BitVec.ofInt InstructionLookupAddressBits
        (instructionImmediate instruction))
    else
      some (BitVec.ofNat InstructionLookupAddressBits
        (BitVec.ofInt Xlen (instructionImmediate instruction)).toNat)
  else
    none

def leftIsPC : JoltISA.Instr → Bool
  | .AUIPC _ _ | .JAL _ _ => true
  | _ => false

def addOperands : JoltISA.Instr → Bool
  | .ADDI _ _ _
  | .LUI _ _
  | .AUIPC _ _
  | .JAL _ _
  | .JALR _ _ _
  | .ADD _ _ _
  | .VirtualPow2 _ _
  | .VirtualPow2W _ _
  | .VirtualPow2I _ _
  | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmask _ _
  | .VirtualShiftRightBitmaskI _ _
  | .VirtualRev8W _ _
  | .VirtualSignExtendWord _ _
  | .VirtualZeroExtendWord _ _
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _ => true
  | _ => false

def subtractOperands : JoltISA.Instr → Bool
  | .SUB _ _ _ => true
  | _ => false

def multiplyOperands : JoltISA.Instr → Bool
  | .MUL _ _ _
  | .MULHU _ _ _
  | .VirtualMULI _ _ _
  | .VirtualAssertMulUNoOverflow _ _ => true
  | _ => false

def adviceOperands : JoltISA.Instr → Bool
  | .VirtualAdvice _ _
  | .VirtualAdviceLoad _ _
  | .VirtualAdviceLen _ _ => true
  | _ => false

def writesLookupOutput : JoltISA.Instr → Bool
  | .JAL _ _ | .JALR _ _ _ | .LD _ _ _ _ => false
  | instruction => (destination instruction).isSome

noncomputable def registerValue
    (state : SailJoltState) (source : Option JoltISA.Src) : BitVec Xlen :=
  match source with
  | some source => sourceValue state source
  | none => 0

noncomputable def destinationRegisterValue
    (state : SailJoltState) (instruction : JoltISA.Instr) : BitVec Xlen :=
  match destination instruction with
  | some destination => destinationValue state destination
  | none => 0

noncomputable def instructionInputs
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before : SailJoltState) : U64 × U128 :=
  let left :=
    if leftIsPC instruction then
      metadata.unexpandedPC
    else
      registerValue before (lookupFirstSource instruction)
  let right :=
    match lookupSecondSource instruction with
    | some source =>
        BitVec.ofNat InstructionLookupAddressBits (sourceValue before source).toNat
    | none => (lowImmediate instruction).getD 0
  (left, right)

def low64 (value : U128) : U64 :=
  BitVec.ofNat Xlen value.toNat

def interleaveAux (left right : U64) : Nat → Nat
  | 0 => 0
  | bit + 1 =>
      interleaveAux left right bit +
        (if left.toNat.testBit bit then 2 ^ (2 * bit + 1) else 0) +
        (if right.toNat.testBit bit then 2 ^ (2 * bit) else 0)

def interleave (left right : U64) : U128 :=
  BitVec.ofNat InstructionLookupAddressBits (interleaveAux left right Xlen)

noncomputable def lookupOperands
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before after : SailJoltState) : U64 × U128 :=
  let inputs := instructionInputs instruction metadata before
  if adviceOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      (destinationRegisterValue after instruction).toNat)
  else if subtractOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      (inputs.1.toNat + 2 ^ Xlen - (low64 inputs.2).toNat))
  else if multiplyOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      (inputs.1.toNat * (low64 inputs.2).toNat))
  else if addOperands instruction then
    match instruction with
    | .AUIPC _ _
    | .VirtualAssertHalfwordAlignment _ _ _
    | .VirtualAssertWordAlignment _ _ _ =>
        (0, BitVec.ofInt InstructionLookupAddressBits
          ((inputs.1.toNat : Int) + inputs.2.toInt))
    | _ =>
        (0, BitVec.ofNat InstructionLookupAddressBits
          (inputs.1.toNat + (low64 inputs.2).toNat))
  else
    (inputs.1, BitVec.ofNat InstructionLookupAddressBits (low64 inputs.2).toNat)

noncomputable def lookupIndex
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before after : SailJoltState) : U128 :=
  let operands := lookupOperands instruction metadata before after
  if addOperands instruction || subtractOperands instruction ||
      multiplyOperands instruction || adviceOperands instruction then
    operands.2
  else
    interleave operands.1 (low64 operands.2)

def boolU64 (value : Bool) : U64 :=
  if value then 1 else 0

noncomputable def lookupOutput
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before after : SailJoltState) : U64 :=
  if writesLookupOutput instruction then
    destinationRegisterValue after instruction
  else
    let inputs := instructionInputs instruction metadata before
    let left := inputs.1
    let right := low64 inputs.2
    match instruction with
    | .JAL _ _ => left + right
    | .JALR _ _ _ =>
        (left + right) &&& BitVec.ofInt Xlen (-2)
    | .BEQ _ _ _ => boolU64 (left == right)
    | .BNE _ _ _ => boolU64 (left != right)
    | .BLT _ _ _ =>
        boolU64 (left.toInt < right.toInt)
    | .BGE _ _ _ =>
        boolU64 (left.toInt ≥ right.toInt)
    | .BLTU _ _ _ => boolU64 (left.toNat < right.toNat)
    | .BGEU _ _ _ => boolU64 (left.toNat ≥ right.toNat)
    | .VirtualAssertEQ _ _ _ => boolU64 (left == right)
    | .VirtualAssertValidDiv0 _ _ =>
        boolU64 (left != 0 || right.toNat == 2 ^ Xlen - 1)
    | .VirtualAssertValidUnsignedRemainder _ _ =>
        boolU64 (right == 0 || left.toNat < right.toNat)
    | .VirtualAssertMulUNoOverflow _ _ =>
        boolU64 (left.toNat * right.toNat ≤ 2 ^ Xlen - 1)
    | .VirtualAssertLTE _ _ => boolU64 (left.toNat ≤ right.toNat)
    | .VirtualAssertHalfwordAlignment _ _ _ =>
        boolU64 ((lookupOperands instruction metadata before after).2.toNat % 2 == 0)
    | .VirtualAssertWordAlignment _ _ _ =>
        boolU64 ((lookupOperands instruction metadata before after).2.toNat % 4 == 0)
    | _ => 0

def fieldBool {F : Type u} [Field F] (value : Bool) : F :=
  if value then 1 else 0

def registerIndicator {F : Type u} [Field F]
    (source : Option JoltISA.Src) (address : RegisterAddress) : F :=
  match source with
  | some source => fieldBool (sourceAddress source == address)
  | none => 0

def destinationIndicator {F : Type u} [Field F]
    (destination : Option JoltISA.Dst) (address : RegisterAddress) : F :=
  match destination with
  | some destination => fieldBool (destinationAddress destination == address)
  | none => 0

noncomputable def rdIncrement
    (instruction : JoltISA.Instr)
    (before after : SailJoltState) : U128 :=
  match destination instruction with
  | some destination =>
      BitVec.ofInt InstructionLookupAddressBits
        (((destinationValue after destination).toNat : Int) -
          (destinationValue before destination).toNat)
  | none => 0

def isNoop : JoltISA.Instr → Bool
  | .NoOp => true
  | _ => false

def isLoad : JoltISA.Instr → Bool
  | .LD _ _ _ _ => true
  | _ => false

def isStore : JoltISA.Instr → Bool
  | .SD _ _ _ => true
  | _ => false

def isJump : JoltISA.Instr → Bool
  | .JAL _ _ | .JALR _ _ _ => true
  | _ => false

def isBranch : JoltISA.Instr → Bool
  | .BEQ _ _ _
  | .BNE _ _ _
  | .BLT _ _ _
  | .BGE _ _ _
  | .BLTU _ _ _
  | .BGEU _ _ _ => true
  | _ => false

def isAssert : JoltISA.Instr → Bool
  | .VirtualAssertEQ _ _ _
  | .VirtualAssertValidDiv0 _ _
  | .VirtualAssertValidUnsignedRemainder _ _
  | .VirtualAssertMulUNoOverflow _ _
  | .VirtualAssertLTE _ _
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _ => true
  | _ => false

def isVirtual (metadata : JoltTraceRowMetadata) : Bool :=
  metadata.virtualSequenceRemaining.isSome

def isLastInSequence (metadata : JoltTraceRowMetadata) : Bool :=
  metadata.virtualSequenceRemaining == some 0

def doNotUpdateUnexpandedPC
    (instruction : JoltISA.Instr) (metadata : JoltTraceRowMetadata) : Bool :=
  isNoop instruction ||
    match metadata.virtualSequenceRemaining with
    | some (_ + 1) => true
    | _ => false

def circuitFlagValue
    (flag : JoltCircuitFlag)
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata) : Bool :=
  match flag with
  | .addOperands => addOperands instruction
  | .subtractOperands => subtractOperands instruction
  | .multiplyOperands => multiplyOperands instruction
  | .load => isLoad instruction
  | .store => isStore instruction
  | .jump => isJump instruction
  | .writeLookupOutputToRD => writesLookupOutput instruction
  | .virtualInstruction => isVirtual metadata
  | .assert => isAssert instruction
  | .doNotUpdateUnexpandedPC => doNotUpdateUnexpandedPC instruction metadata
  | .advice => adviceOperands instruction
  | .isCompressed => metadata.isCompressed
  | .isFirstInSequence => metadata.isFirstInSequence
  | .isLastInSequence => isLastInSequence metadata

def instructionFlagValue
    (flag : JoltInstructionFlag) (instruction : JoltISA.Instr) : Bool :=
  match flag with
  | .leftOperandIsPC => leftIsPC instruction
  | .rightOperandIsImm => rightOperandIsImmediate instruction
  | .leftOperandIsRs1Value => (lookupFirstSource instruction).isSome
  | .rightOperandIsRs2Value => (lookupSecondSource instruction).isSome
  | .branch => isBranch instruction
  | .isNoop => isNoop instruction

def lookupTable : JoltISA.Instr → Option JoltLookupTable
  | .ADDI _ _ _
  | .LUI _ _
  | .AUIPC _ _
  | .JAL _ _
  | .ADD _ _ _
  | .SUB _ _ _
  | .MUL _ _ _
  | .VirtualMULI _ _ _
  | .VirtualAdvice _ _
  | .VirtualAdviceLoad _ _
  | .VirtualAdviceLen _ _ => some .RangeCheck
  | .JALR _ _ _ => some .RangeCheckAligned
  | .ANDI _ _ _ | .AND _ _ _ => some .AND
  | .ANDN _ _ _ => some .ANDN
  | .ORI _ _ _ | .OR _ _ _ => some .OR
  | .XORI _ _ _ | .XOR _ _ _ => some .XOR
  | .BEQ _ _ _ | .VirtualAssertEQ _ _ _ => some .Equal
  | .BGE _ _ _ => some .SignedGreaterThanEqual
  | .BGEU _ _ _ => some .UnsignedGreaterThanEqual
  | .BNE _ _ _ => some .NotEqual
  | .SLTI _ _ _ | .BLT _ _ _ | .SLT _ _ _ => some .SignedLessThan
  | .SLTIU _ _ _ | .BLTU _ _ _ | .SLTU _ _ _ => some .UnsignedLessThan
  | .VirtualMovsign _ _ => some .SignMask
  | .MULHU _ _ _ => some .UpperWord
  | .VirtualAssertLTE _ _ => some .UnsignedLessThanEqual
  | .VirtualAssertValidUnsignedRemainder _ _ => some .ValidUnsignedRemainder
  | .VirtualAssertValidDiv0 _ _ => some .ValidDiv0
  | .VirtualAssertHalfwordAlignment _ _ _ => some .HalfwordAlignment
  | .VirtualAssertWordAlignment _ _ _ => some .WordAlignment
  | .VirtualZeroExtendWord _ _ => some .LowerHalfWord
  | .VirtualSignExtendWord _ _ => some .SignExtendHalfWord
  | .VirtualPow2 _ _ | .VirtualPow2I _ _ => some .Pow2
  | .VirtualPow2W _ _ | .VirtualPow2IW _ _ => some .Pow2W
  | .VirtualShiftRightBitmask _ _
  | .VirtualShiftRightBitmaskI _ _ => some .ShiftRightBitmask
  | .VirtualRev8W _ _ => some .VirtualRev8W
  | .VirtualSRL _ _ _ | .VirtualSRLI _ _ _ => some .VirtualSRL
  | .VirtualSRA _ _ _ | .VirtualSRAI _ _ _ => some .VirtualSRA
  | .VirtualROTRI _ _ _ => some .VirtualROTR
  | .VirtualROTRIW _ _ _ => some .VirtualROTRW
  | .VirtualChangeDivisor _ _ _ => some .VirtualChangeDivisor
  | .VirtualChangeDivisorW _ _ _ => some .VirtualChangeDivisorW
  | .VirtualAssertMulUNoOverflow _ _ => some .MulUNoOverflow
  | .VirtualXORROT32 _ _ _ => some .VirtualXORROT32
  | .VirtualXORROT24 _ _ _ => some .VirtualXORROT24
  | .VirtualXORROT16 _ _ _ => some .VirtualXORROT16
  | .VirtualXORROT63 _ _ _ => some .VirtualXORROT63
  | .VirtualXORROTW16 _ _ _ => some .VirtualXORROTW16
  | .VirtualXORROTW12 _ _ _ => some .VirtualXORROTW12
  | .VirtualXORROTW8 _ _ _ => some .VirtualXORROTW8
  | .VirtualXORROTW7 _ _ _ => some .VirtualXORROTW7
  | _ => none

def nextTraceIndex {T : Nat} (i : Fin T) : Option (Fin T) :=
  if h : i.val + 1 < T then some ⟨i.val + 1, h⟩ else none

def nextMetadata {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (i : Fin params.traceLength) : Option JoltTraceRowMetadata :=
  (nextTraceIndex i).map trace.metadata.row

def nextInstruction {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (i : Fin params.traceLength) : Option JoltISA.Instr :=
  (nextTraceIndex i).map trace.instrList

def finalState {params : JoltWitnessParams}
    (trace : HonestTrace params) : SailJoltState :=
  trace.state ⟨params.traceLength, Nat.lt_succ_self params.traceLength⟩

def memoryByte (state : SailJoltState) (address : Nat) : BitVec 8 :=
  (state.sail.mem.get? address).getD 0

def memoryWord (state : SailJoltState) (address : Nat) : U64 :=
  BitVec.ofNat Xlen
    ((memoryByte state address).toNat +
      (memoryByte state (address + 1)).toNat * 2 ^ 8 +
      (memoryByte state (address + 2)).toNat * 2 ^ 16 +
      (memoryByte state (address + 3)).toNat * 2 ^ 24 +
      (memoryByte state (address + 4)).toNat * 2 ^ 32 +
      (memoryByte state (address + 5)).toNat * 2 ^ 40 +
      (memoryByte state (address + 6)).toNat * 2 ^ 48 +
      (memoryByte state (address + 7)).toNat * 2 ^ 56)

noncomputable def registerAtAddress
    (state : SailJoltState) (address : RegisterAddress) : U64 :=
  if address.val < 32 then
    sourceValue state (.xreg (.Regidx (BitVec.ofNat 5 address.val)))
  else
    sourceValue state (.vreg (BitVec.ofNat RegisterAddressBits address.val))

noncomputable def ramAccessAddress
    (instruction : JoltISA.Instr) (before : SailJoltState) : Option U64 :=
  match instruction with
  | .LD _ _ base immediate =>
      some (sourceValue before base + sign_extend (m := Xlen) immediate)
  | .SD base _ immediate =>
      some (sourceValue before base + sign_extend (m := Xlen) immediate)
  | _ => none

noncomputable def remappedRamAddress
    {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (instruction : JoltISA.Instr)
    (before : SailJoltState) : Option Nat :=
  match ramAccessAddress instruction before with
  | some address =>
      if address == 0 || address.toNat < trace.metadata.lowestMemoryAddress.toNat then
        none
      else
        some ((address.toNat - trace.metadata.lowestMemoryAddress.toNat) / 8)
  | none => none

noncomputable def ramReadValue
    (instruction : JoltISA.Instr)
    (before : SailJoltState) : U64 :=
  match ramAccessAddress instruction before with
  | some address => memoryWord before address.toNat
  | none => 0

noncomputable def ramWriteValue
    (instruction : JoltISA.Instr)
    (before after : SailJoltState) : U64 :=
  if isLoad instruction then
    ramReadValue instruction before
  else
    match ramAccessAddress instruction before with
    | some address => memoryWord after address.toNat
    | none => 0

noncomputable def ramIncrement
    (instruction : JoltISA.Instr)
    (before after : SailJoltState) : U128 :=
  if isStore instruction then
    BitVec.ofInt InstructionLookupAddressBits
      (((ramWriteValue instruction before after).toNat : Int) -
        (ramReadValue instruction before).toNat)
  else
    0

def raChunk (value index chunks chunkBits : Nat) : Nat :=
  (value / 2 ^ ((chunks - (index + 1)) * chunkBits)) % 2 ^ chunkBits

def oneHot {F : Type u} [Field F] (actual expected : Nat) : F :=
  fieldBool (actual == expected)

noncomputable def productValue
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before : SailJoltState) : Int :=
  let inputs := instructionInputs instruction metadata before
  (inputs.1.toNat : Int) * inputs.2.toInt

noncomputable def honest_witness
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) : JoltWitness params F where
  committed := fun polynomial =>
    match polynomial with
    | .rdInc => fun i =>
        fieldFromI128
          (rdIncrement (trace.instrList i) (trace.preState i) (trace.postState i))
    | .ramInc => fun i =>
        fieldFromI128
          (ramIncrement (trace.instrList i) (trace.preState i) (trace.postState i))
    | .instructionRa chunk => fun address i =>
        oneHot address.val
          (raChunk
            (lookupIndex
              (trace.instrList i)
              (trace.metadata.row i)
              (trace.preState i)
              (trace.postState i)).toNat
            chunk.val
            params.instructionCommittedRaCount
            params.committedChunkBits)
    | .bytecodeRa chunk => fun address i =>
        oneHot address.val
          (raChunk
            (trace.metadata.row i).pc
            chunk.val
            params.bytecodeCommittedRaCount
            params.committedChunkBits)
    | .ramRa chunk => fun address i =>
        match remappedRamAddress trace (trace.instrList i) (trace.preState i) with
        | some ramAddress =>
            oneHot address.val
              (raChunk
                ramAddress
                chunk.val
                params.ramCommittedRaCount
                params.committedChunkBits)
        | none => 0
    | .trustedAdvice _ => fun i =>
        fieldFromU64 (trace.metadata.trustedAdvice i)
    | .untrustedAdvice _ => fun i =>
        fieldFromU64 (trace.metadata.untrustedAdvice i)

  virtual := fun polynomial =>
    match polynomial with
    | .pc => fun i => ((trace.metadata.row i).pc : F)
    | .unexpandedPC => fun i =>
        fieldFromU64 (trace.metadata.row i).unexpandedPC
    | .nextPC => fun i =>
        match nextMetadata trace i with
        | some metadata => (metadata.pc : F)
        | none => 0
    | .nextUnexpandedPC => fun i =>
        match nextMetadata trace i with
        | some metadata => fieldFromU64 metadata.unexpandedPC
        | none => 0
    | .nextIsNoop => fun i =>
        fieldBool <| match nextInstruction trace i with
        | some instruction => isNoop instruction
        | none => false
    | .nextIsVirtual => fun i =>
        fieldBool <| match nextMetadata trace i with
        | some metadata => isVirtual metadata
        | none => false
    | .nextIsFirstInSequence => fun i =>
        fieldBool <| match nextMetadata trace i with
        | some metadata => metadata.isFirstInSequence
        | none => false
    | .leftLookupOperand => fun i =>
        fieldFromU64
          (lookupOperands
            (trace.instrList i)
            (trace.metadata.row i)
            (trace.preState i)
            (trace.postState i)).1
    | .rightLookupOperand => fun i =>
        fieldFromU128
          (lookupOperands
            (trace.instrList i)
            (trace.metadata.row i)
            (trace.preState i)
            (trace.postState i)).2
    | .leftInstructionInput => fun i =>
        fieldFromU64
          (instructionInputs
            (trace.instrList i) (trace.metadata.row i) (trace.preState i)).1
    | .rightInstructionInput => fun i =>
        fieldFromI128
          (instructionInputs
            (trace.instrList i) (trace.metadata.row i) (trace.preState i)).2
    | .product => fun i =>
        fieldFromInt
          (productValue
            (trace.instrList i) (trace.metadata.row i) (trace.preState i))
    | .shouldJump => fun i =>
        fieldBool <| isJump (trace.instrList i) &&
          match nextInstruction trace i with
          | some instruction => !(isNoop instruction)
          | none => true
    | .shouldBranch => fun i =>
        fieldBool <| isBranch (trace.instrList i) &&
          lookupOutput
            (trace.instrList i)
            (trace.metadata.row i)
            (trace.preState i)
            (trace.postState i) == 1
    | .imm => fun i =>
        fieldFromInt (instructionImmediate (trace.instrList i))
    | .rs1Value => fun i =>
        fieldFromU64
          (registerValue (trace.preState i) (firstSource (trace.instrList i)))
    | .rs2Value => fun i =>
        fieldFromU64
          (registerValue (trace.preState i) (secondSource (trace.instrList i)))
    | .rdWriteValue => fun i =>
        fieldFromU64
          (destinationRegisterValue (trace.postState i) (trace.instrList i))
    | .lookupOutput => fun i =>
        fieldFromU64
          (lookupOutput
            (trace.instrList i)
            (trace.metadata.row i)
            (trace.preState i)
            (trace.postState i))
    | .instructionRafFlag => fun i =>
        fieldBool (addOperands (trace.instrList i) ||
          subtractOperands (trace.instrList i) ||
          multiplyOperands (trace.instrList i) ||
          adviceOperands (trace.instrList i))
    | .rs1Ra => fun address i =>
        registerIndicator (firstSource (trace.instrList i)) address
    | .rs2Ra => fun address i =>
        registerIndicator (secondSource (trace.instrList i)) address
    | .rdWa => fun address i =>
        destinationIndicator (destination (trace.instrList i)) address
    | .instructionRa chunk => fun address i =>
        oneHot address.val
          (raChunk
            (lookupIndex
              (trace.instrList i)
              (trace.metadata.row i)
              (trace.preState i)
              (trace.postState i)).toNat
            chunk.val
            params.instructionVirtualRaCount
            params.lookupVirtualChunkBits)
    | .registersVal => fun address i =>
        fieldFromU64 (registerAtAddress (trace.preState i) address)
    | .ramAddress => fun i =>
        fieldFromU64
          ((ramAccessAddress (trace.instrList i) (trace.preState i)).getD 0)
    | .ramRa => fun address i =>
        match remappedRamAddress trace (trace.instrList i) (trace.preState i) with
        | some ramAddress => oneHot address.val ramAddress
        | none => 0
    | .ramReadValue => fun i =>
        fieldFromU64 (ramReadValue (trace.instrList i) (trace.preState i))
    | .ramWriteValue => fun i =>
        fieldFromU64
          (ramWriteValue
            (trace.instrList i) (trace.preState i) (trace.postState i))
    | .ramVal => fun address i =>
        fieldFromU64
          (memoryWord
            (trace.preState i)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val))
    | .ramValFinal => fun address =>
        fieldFromU64
          (memoryWord
            (finalState trace)
            (trace.metadata.lowestMemoryAddress.toNat + 8 * address.val))
    | .ramHammingWeight => fun i =>
        fieldBool <| match ramAccessAddress (trace.instrList i) (trace.preState i) with
        | some address => address != 0
        | none => false
    | .opFlag flag => fun i =>
        fieldBool
          (circuitFlagValue flag (trace.instrList i) (trace.metadata.row i))
    | .instructionFlag flag => fun i =>
        fieldBool (instructionFlagValue flag (trace.instrList i))
    | .lookupTableFlag table => fun i =>
        fieldBool (lookupTable (trace.instrList i) == some table)

end HonestWitness

export HonestWitness (honest_witness)

end JoltConstraints
