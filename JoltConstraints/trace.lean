import JoltConstraints.lookup_table

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

/-- Rust assigns architectural registers to `0..31` and permits virtual
register operands only in the remaining part of the seven-bit domain. -/
def sourceAddressValid : JoltISA.Src → Prop
  | .xreg _ => True
  | .vreg register => 32 ≤ register.toNat

def destinationAddress (destination : JoltISA.Dst) : RegisterAddress :=
  sourceAddress (destinationSource destination)

def destinationAddressValid (destination : JoltISA.Dst) : Prop :=
  sourceAddressValid (destinationSource destination)

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
  | .NoOp
  | .BEQ ..
  | .BNE ..
  | .BLT ..
  | .BGE ..
  | .BLTU ..
  | .BGEU ..
  | .FENCE
  | .SD ..
  | .VirtualAssertHalfwordAlignment ..
  | .VirtualAssertWordAlignment ..
  | .VirtualHostIO
  | .VirtualAssertEQ ..
  | .VirtualAssertValidDiv0 ..
  | .VirtualAssertValidUnsignedRemainder ..
  | .VirtualAssertMulUNoOverflow ..
  | .VirtualAssertLTE .. => none

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
  | .NoOp
  | .LUI ..
  | .AUIPC ..
  | .JAL ..
  | .FENCE
  | .VirtualPow2I ..
  | .VirtualPow2IW ..
  | .VirtualShiftRightBitmaskI ..
  | .VirtualAdvice ..
  | .VirtualAdviceLoad ..
  | .VirtualAdviceLen ..
  | .VirtualHostIO => none

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
  | .NoOp
  | .ADDI ..
  | .ANDI ..
  | .ORI ..
  | .XORI ..
  | .SLTI ..
  | .SLTIU ..
  | .LUI ..
  | .AUIPC ..
  | .JAL ..
  | .JALR ..
  | .FENCE
  | .VirtualMULI ..
  | .VirtualPow2 ..
  | .VirtualPow2W ..
  | .VirtualPow2I ..
  | .VirtualPow2IW ..
  | .VirtualShiftRightBitmask ..
  | .VirtualShiftRightBitmaskI ..
  | .VirtualSRLI ..
  | .VirtualSRAI ..
  | .VirtualROTRI ..
  | .VirtualROTRIW ..
  | .VirtualRev8W ..
  | .VirtualSignExtendWord ..
  | .VirtualZeroExtendWord ..
  | .VirtualMovsign ..
  | .VirtualAssertHalfwordAlignment ..
  | .VirtualAssertWordAlignment ..
  | .LD ..
  | .VirtualAdvice ..
  | .VirtualAdviceLoad ..
  | .VirtualAdviceLen ..
  | .VirtualHostIO => none

def lookupFirstSource (instruction : JoltISA.Instr) : Option JoltISA.Src :=
  match instruction with
  | .LD _ _ _ _ | .SD _ _ _ => none
  | _ => firstSource instruction

def lookupSecondSource (instruction : JoltISA.Instr) : Option JoltISA.Src :=
  match instruction with
  | .SD _ _ _ => none
  | _ => secondSource instruction

/-- Reconstruct the Rust-normalized static immediate when the executable Lean
instruction still contains that information.  This is not a uniform signed
offset: ordinary I/U/J formats normalize through `u64`, whereas load, store,
branch, and alignment formats retain a signed value.

The three advice instructions are exceptional.  Their executable Lean
constructors carry a runtime result where Rust's proof-facing row retains the
static `imm`; `JoltTraceRow.Valid` therefore does not identify those values. -/
def instructionImmediate : JoltISA.Instr → Int
  | .ADDI _ _ immediate
  | .ANDI _ _ immediate
  | .ORI _ _ immediate
  | .XORI _ _ immediate
  | .SLTI _ _ immediate
  | .SLTIU _ _ immediate
  | .JALR _ _ immediate =>
      ((sign_extend (m := Xlen) immediate).toNat : Int)
  | .LD _ _ _ immediate
  | .SD _ _ immediate =>
      (sign_extend (m := Xlen) immediate).toInt
  | .LUI _ immediate => (immediate.toNat : Int)
  | .AUIPC _ immediate =>
      ((sign_extend (m := Xlen)
        (immediate +++ (0 : BitVec 12))).toNat : Int)
  | .JAL _ immediate =>
      ((sign_extend (m := Xlen) immediate).toNat : Int)
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
  | .NoOp
  | .FENCE
  | .ADD ..
  | .SUB ..
  | .MUL ..
  | .MULHU ..
  | .ANDN ..
  | .VirtualPow2 ..
  | .VirtualPow2W ..
  | .VirtualShiftRightBitmask ..
  | .VirtualSRL ..
  | .VirtualSRA ..
  | .VirtualRev8W ..
  | .VirtualXORROT32 ..
  | .VirtualXORROT24 ..
  | .VirtualXORROT16 ..
  | .VirtualXORROT63 ..
  | .VirtualXORROTW16 ..
  | .VirtualXORROTW12 ..
  | .VirtualXORROTW8 ..
  | .VirtualXORROTW7 ..
  | .OR ..
  | .XOR ..
  | .AND ..
  | .SLT ..
  | .SLTU ..
  | .VirtualSignExtendWord ..
  | .VirtualZeroExtendWord ..
  | .VirtualAdvice ..
  | .VirtualAdviceLoad ..
  | .VirtualAdviceLen ..
  | .VirtualHostIO
  | .VirtualAssertValidDiv0 ..
  | .VirtualChangeDivisor ..
  | .VirtualChangeDivisorW ..
  | .VirtualAssertValidUnsignedRemainder ..
  | .VirtualAssertMulUNoOverflow ..
  | .VirtualAssertLTE .. => 0

/-- The static immediate agrees with what can be reconstructed from execution
semantics.  Advice rows deliberately form the exception: their Lean execution
operand is a runtime advice result, while the proof row stores static bytecode
data (for example the byte width of `VirtualAdviceLoad`). -/
def instructionImmediateMatches (row : JoltTraceRow) : Prop :=
  match row.instruction with
  | .VirtualAdvice ..
  | .VirtualAdviceLoad ..
  | .VirtualAdviceLen .. => True
  | instruction =>
      row.instructionRow.operands.imm = instructionImmediate instruction

/-- Exact correspondence between Rust's normalized register operands and the
execution instruction.  `VirtualAdviceLen` is the sole final instruction whose
Rust `FormatI` row contains an `rs1` lane that the executable Lean constructor
does not retain; its presence is still recorded explicitly. -/
def instructionRegisterOperandsMatch (row : JoltTraceRow) : Prop :=
  let operands := row.instructionRow.operands
  match row.instruction with
  | .VirtualAdviceLen destination _ =>
      operands.rs1.isSome = true ∧
        operands.rs2 = none ∧
        operands.rd = some (destinationAddress destination)
  | instruction =>
      operands.rs1 = (firstSource instruction).map sourceAddress ∧
        operands.rs2 = (secondSource instruction).map sourceAddress ∧
        operands.rd = (destination instruction).map destinationAddress

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

def lowImmediate (row : JoltTraceRow) : Option U128 :=
  let instruction := row.instruction
  if rightOperandIsImmediate instruction then
    if signedInstructionImmediate instruction then
      some (BitVec.ofInt InstructionLookupAddressBits
        row.instructionRow.operands.imm)
    else
      some (BitVec.ofNat InstructionLookupAddressBits
        (BitVec.ofInt Xlen row.instructionRow.operands.imm).toNat)
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

def instructionInputs (row : JoltTraceRow) : U64 × U128 :=
  let instruction := row.instruction
  let left :=
    if leftIsPC instruction then
      row.metadata.unexpandedPC
    else
      if (lookupFirstSource instruction).isSome then row.rs1Value else 0
  let right :=
    if (lookupSecondSource instruction).isSome then
      BitVec.ofNat InstructionLookupAddressBits row.rs2Value.toNat
    else
      (lowImmediate row).getD 0
  (left, right)

def low64 (value : U128) : U64 :=
  BitVec.ofNat Xlen value.toNat

def interleave (left right : U64) : U128 :=
  InstructionLookupAddress.interleaveBits left right

def lookupOperands (row : JoltTraceRow) : U64 × U128 :=
  let instruction := row.instruction
  let inputs := instructionInputs row
  if adviceOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      row.rdWriteValue.toNat)
  else if subtractOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      (inputs.1.toNat + 2 ^ Xlen - (low64 inputs.2).toNat))
  else if multiplyOperands instruction then
    (0, BitVec.ofNat InstructionLookupAddressBits
      (inputs.1.toNat * (low64 inputs.2).toNat))
  else if addOperands instruction then
    if signedInstructionImmediate instruction then
      (0, BitVec.ofInt InstructionLookupAddressBits
        ((inputs.1.toNat : Int) + inputs.2.toInt))
    else
      (0, BitVec.ofNat InstructionLookupAddressBits
        (inputs.1.toNat + (low64 inputs.2).toNat))
  else
    (inputs.1, BitVec.ofNat InstructionLookupAddressBits (low64 inputs.2).toNat)

def lookupIndex (row : JoltTraceRow) : U128 :=
  let instruction := row.instruction
  let operands := lookupOperands row
  if addOperands instruction || subtractOperands instruction ||
      multiplyOperands instruction || adviceOperands instruction then
    operands.2
  else
    interleave operands.1 (low64 operands.2)

def boolU64 (value : Bool) : U64 :=
  if value then 1 else 0

def lookupOutput (row : JoltTraceRow) : U64 :=
  let instruction := row.instruction
  if writesLookupOutput instruction then
    row.rdWriteValue
  else
    let inputs := instructionInputs row
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
        boolU64 ((lookupOperands row).2.toNat % 2 == 0)
    | .VirtualAssertWordAlignment _ _ _ =>
        boolU64 ((lookupOperands row).2.toNat % 4 == 0)
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

/-- One-hot register selector from the exact proof-facing normalized operand. -/
def registerAddressIndicator {F : Type u} [Field F]
    (register : Option RegisterAddress) (address : RegisterAddress) : F :=
  match register with
  | some register => fieldBool (register == address)
  | none => 0

def rdIncrement (row : JoltTraceRow) : U128 :=
  match row.instructionRow.operands.rd with
  | some _ =>
      BitVec.ofInt InstructionLookupAddressBits
        (((row.rdWriteValue.toNat : Int) - row.rdPreValue.toNat))
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

/-- Rust's read-RAF flag: combined-address ADD/SUB/MUL/advice lookups use the
full lookup address, while ordinary two-input tables use interleaved operands. -/
def instructionRafFlagValue (instruction : JoltISA.Instr) : Bool :=
  addOperands instruction || subtractOperands instruction ||
    multiplyOperands instruction || adviceOperands instruction

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

end HonestWitness

/-! ## Static bytecode-row interpretation

Rust derives the bytecode read-RAF table values from the final instruction
kind stored in each public `JoltInstructionRow`.  The executable Lean
instruction is deliberately absent from `JoltPublicInputs.bytecode`, so these
kind-level classifiers are the public-table counterparts of the extraction
classifiers above.  The exhaustive correspondence lemmas below keep the two
views synchronized and make ISA drift fail at compile time. -/

namespace JoltInstructionKind

def addOperands : JoltInstructionKind → Bool
  | .ADDI | .LUI | .AUIPC | .JAL | .JALR | .ADD
  | .VirtualPow2 | .VirtualPow2W | .VirtualPow2I | .VirtualPow2IW
  | .VirtualShiftRightBitmask | .VirtualShiftRightBitmaskI
  | .VirtualRev8W | .VirtualSignExtendWord | .VirtualZeroExtendWord
  | .VirtualAssertHalfwordAlignment | .VirtualAssertWordAlignment => true
  | _ => false

def subtractOperands : JoltInstructionKind → Bool
  | .SUB => true
  | _ => false

def multiplyOperands : JoltInstructionKind → Bool
  | .MUL | .MULHU | .VirtualMULI | .VirtualAssertMulUNoOverflow => true
  | _ => false

def isLoad : JoltInstructionKind → Bool
  | .LD => true
  | _ => false

def isStore : JoltInstructionKind → Bool
  | .SD => true
  | _ => false

def isJump : JoltInstructionKind → Bool
  | .JAL | .JALR => true
  | _ => false

def writesLookupOutput : JoltInstructionKind → Bool
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .LUI | .AUIPC
  | .ADD | .SUB | .MUL | .MULHU | .ANDN | .VirtualMULI
  | .VirtualPow2 | .VirtualPow2W | .VirtualPow2I | .VirtualPow2IW
  | .VirtualShiftRightBitmask | .VirtualShiftRightBitmaskI
  | .VirtualSRLI | .VirtualSRAI | .VirtualSRL | .VirtualSRA
  | .VirtualROTRI | .VirtualROTRIW | .VirtualRev8W
  | .VirtualXORROT32 | .VirtualXORROT24 | .VirtualXORROT16
  | .VirtualXORROT63 | .VirtualXORROTW16 | .VirtualXORROTW12
  | .VirtualXORROTW8 | .VirtualXORROTW7
  | .OR | .XOR | .AND | .SLT | .SLTU
  | .VirtualSignExtendWord | .VirtualZeroExtendWord | .VirtualMovsign
  | .VirtualAdvice | .VirtualAdviceLoad | .VirtualAdviceLen
  | .VirtualChangeDivisor | .VirtualChangeDivisorW => true
  | _ => false

def isAssert : JoltInstructionKind → Bool
  | .VirtualAssertEQ | .VirtualAssertValidDiv0
  | .VirtualAssertValidUnsignedRemainder | .VirtualAssertMulUNoOverflow
  | .VirtualAssertLTE | .VirtualAssertHalfwordAlignment
  | .VirtualAssertWordAlignment => true
  | _ => false

def adviceOperands : JoltInstructionKind → Bool
  | .VirtualAdvice | .VirtualAdviceLoad | .VirtualAdviceLen => true
  | _ => false

def leftIsPC : JoltInstructionKind → Bool
  | .AUIPC | .JAL => true
  | _ => false

def rightOperandIsImmediate : JoltInstructionKind → Bool
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .LUI | .AUIPC
  | .JAL | .JALR | .VirtualMULI | .VirtualPow2I | .VirtualPow2IW
  | .VirtualShiftRightBitmaskI | .VirtualSRLI | .VirtualSRAI
  | .VirtualROTRI | .VirtualROTRIW | .VirtualMovsign
  | .VirtualAssertHalfwordAlignment | .VirtualAssertWordAlignment => true
  | _ => false

def lookupFirstSourceIsSome : JoltInstructionKind → Bool
  | .ADDI | .ANDI | .ORI | .XORI | .SLTI | .SLTIU | .JALR
  | .VirtualMULI | .VirtualPow2 | .VirtualPow2W
  | .VirtualShiftRightBitmask | .VirtualSRLI | .VirtualSRAI
  | .VirtualROTRI | .VirtualROTRIW | .VirtualRev8W
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU
  | .ADD | .SUB | .MUL | .MULHU | .ANDN | .VirtualSRL | .VirtualSRA
  | .VirtualXORROT32 | .VirtualXORROT24 | .VirtualXORROT16
  | .VirtualXORROT63 | .VirtualXORROTW16 | .VirtualXORROTW12
  | .VirtualXORROTW8 | .VirtualXORROTW7
  | .OR | .XOR | .AND | .SLT | .SLTU
  | .VirtualSignExtendWord | .VirtualZeroExtendWord | .VirtualMovsign
  | .VirtualAssertEQ | .VirtualAssertValidDiv0
  | .VirtualChangeDivisor | .VirtualChangeDivisorW
  | .VirtualAssertValidUnsignedRemainder | .VirtualAssertMulUNoOverflow
  | .VirtualAssertLTE | .VirtualAssertHalfwordAlignment
  | .VirtualAssertWordAlignment => true
  | _ => false

def lookupSecondSourceIsSome : JoltInstructionKind → Bool
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU
  | .ADD | .SUB | .MUL | .MULHU | .ANDN | .VirtualSRL | .VirtualSRA
  | .VirtualXORROT32 | .VirtualXORROT24 | .VirtualXORROT16
  | .VirtualXORROT63 | .VirtualXORROTW16 | .VirtualXORROTW12
  | .VirtualXORROTW8 | .VirtualXORROTW7
  | .OR | .XOR | .AND | .SLT | .SLTU
  | .VirtualAssertEQ | .VirtualAssertValidDiv0
  | .VirtualChangeDivisor | .VirtualChangeDivisorW
  | .VirtualAssertValidUnsignedRemainder | .VirtualAssertMulUNoOverflow
  | .VirtualAssertLTE => true
  | _ => false

def isBranch : JoltInstructionKind → Bool
  | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU => true
  | _ => false

def isNoop : JoltInstructionKind → Bool
  | .NoOp => true
  | _ => false

def lookupTable : JoltInstructionKind → Option JoltLookupTable
  | .ADDI | .LUI | .AUIPC | .JAL | .ADD | .SUB | .MUL | .VirtualMULI
  | .VirtualAdvice | .VirtualAdviceLoad | .VirtualAdviceLen =>
      some .RangeCheck
  | .JALR => some .RangeCheckAligned
  | .ANDI | .AND => some .AND
  | .ANDN => some .ANDN
  | .ORI | .OR => some .OR
  | .XORI | .XOR => some .XOR
  | .BEQ | .VirtualAssertEQ => some .Equal
  | .BGE => some .SignedGreaterThanEqual
  | .BGEU => some .UnsignedGreaterThanEqual
  | .BNE => some .NotEqual
  | .SLTI | .BLT | .SLT => some .SignedLessThan
  | .SLTIU | .BLTU | .SLTU => some .UnsignedLessThan
  | .VirtualMovsign => some .SignMask
  | .MULHU => some .UpperWord
  | .VirtualAssertLTE => some .UnsignedLessThanEqual
  | .VirtualAssertValidUnsignedRemainder => some .ValidUnsignedRemainder
  | .VirtualAssertValidDiv0 => some .ValidDiv0
  | .VirtualAssertHalfwordAlignment => some .HalfwordAlignment
  | .VirtualAssertWordAlignment => some .WordAlignment
  | .VirtualZeroExtendWord => some .LowerHalfWord
  | .VirtualSignExtendWord => some .SignExtendHalfWord
  | .VirtualPow2 | .VirtualPow2I => some .Pow2
  | .VirtualPow2W | .VirtualPow2IW => some .Pow2W
  | .VirtualShiftRightBitmask | .VirtualShiftRightBitmaskI =>
      some .ShiftRightBitmask
  | .VirtualRev8W => some .VirtualRev8W
  | .VirtualSRL | .VirtualSRLI => some .VirtualSRL
  | .VirtualSRA | .VirtualSRAI => some .VirtualSRA
  | .VirtualROTRI => some .VirtualROTR
  | .VirtualROTRIW => some .VirtualROTRW
  | .VirtualChangeDivisor => some .VirtualChangeDivisor
  | .VirtualChangeDivisorW => some .VirtualChangeDivisorW
  | .VirtualAssertMulUNoOverflow => some .MulUNoOverflow
  | .VirtualXORROT32 => some .VirtualXORROT32
  | .VirtualXORROT24 => some .VirtualXORROT24
  | .VirtualXORROT16 => some .VirtualXORROT16
  | .VirtualXORROT63 => some .VirtualXORROT63
  | .VirtualXORROTW16 => some .VirtualXORROTW16
  | .VirtualXORROTW12 => some .VirtualXORROTW12
  | .VirtualXORROTW8 => some .VirtualXORROTW8
  | .VirtualXORROTW7 => some .VirtualXORROTW7
  | _ => none

end JoltInstructionKind

namespace JoltBytecodeRow

/-- One public circuit-flag table column in Rust's bytecode read-RAF. -/
def circuitFlagValue (row : JoltBytecodeRow) (flag : JoltCircuitFlag) : Bool :=
  match flag with
  | .addOperands => row.instruction.kind.addOperands
  | .subtractOperands => row.instruction.kind.subtractOperands
  | .multiplyOperands => row.instruction.kind.multiplyOperands
  | .load => row.instruction.kind.isLoad
  | .store => row.instruction.kind.isStore
  | .jump => row.instruction.kind.isJump
  | .writeLookupOutputToRD => row.instruction.kind.writesLookupOutput
  | .virtualInstruction => row.virtualSequenceRemaining.isSome
  | .assert => row.instruction.kind.isAssert
  | .doNotUpdateUnexpandedPC =>
      row.instruction.kind.isNoop ||
        match row.virtualSequenceRemaining with
        | some (_ + 1) => true
        | _ => false
  | .advice => row.instruction.kind.adviceOperands
  | .isCompressed => row.isCompressed
  | .isFirstInSequence => row.isFirstInSequence
  | .isLastInSequence => row.virtualSequenceRemaining == some 0

/-- One public instruction-routing-flag table column. -/
def instructionFlagValue
    (row : JoltBytecodeRow) (flag : JoltInstructionFlag) : Bool :=
  match flag with
  | .leftOperandIsPC => row.instruction.kind.leftIsPC
  | .rightOperandIsImm => row.instruction.kind.rightOperandIsImmediate
  | .leftOperandIsRs1Value => row.instruction.kind.lookupFirstSourceIsSome
  | .rightOperandIsRs2Value => row.instruction.kind.lookupSecondSourceIsSome
  | .branch => row.instruction.kind.isBranch
  | .isNoop => row.instruction.kind.isNoop

/-- Public selector for Rust's combined-address instruction read-RAF mode. -/
def instructionRafFlagValue (row : JoltBytecodeRow) : Bool :=
  row.instruction.kind.addOperands ||
    row.instruction.kind.subtractOperands ||
    row.instruction.kind.multiplyOperands ||
    row.instruction.kind.adviceOperands

/-- Public lookup-table selection derived from the final instruction kind. -/
def lookupTable (row : JoltBytecodeRow) : Option JoltLookupTable :=
  row.instruction.kind.lookupTable

end JoltBytecodeRow

namespace HonestWitness

@[simp] theorem JoltInstructionKind.addOperands_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).addOperands =
      addOperands instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.subtractOperands_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).subtractOperands =
      subtractOperands instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.multiplyOperands_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).multiplyOperands =
      multiplyOperands instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isLoad_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isLoad =
      isLoad instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isStore_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isStore =
      isStore instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isJump_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isJump =
      isJump instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.writesLookupOutput_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).writesLookupOutput =
      writesLookupOutput instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isAssert_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isAssert =
      isAssert instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.adviceOperands_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).adviceOperands =
      adviceOperands instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.leftIsPC_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).leftIsPC =
      leftIsPC instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.rightOperandIsImmediate_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).rightOperandIsImmediate =
      rightOperandIsImmediate instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.lookupFirstSourceIsSome_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).lookupFirstSourceIsSome =
      (lookupFirstSource instruction).isSome := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.lookupSecondSourceIsSome_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).lookupSecondSourceIsSome =
      (lookupSecondSource instruction).isSome := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isBranch_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isBranch =
      isBranch instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.isNoop_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).isNoop =
      isNoop instruction := by cases instruction <;> rfl

@[simp] theorem JoltInstructionKind.lookupTable_ofInstr
    (instruction : JoltISA.Instr) :
    (JoltInstructionKind.ofInstr instruction).lookupTable =
      lookupTable instruction := by cases instruction <;> rfl

theorem circuitFlagValue_eq_bytecodeRow
    (row : JoltTraceRow) (flag : JoltCircuitFlag)
    (kindEq : row.instructionRow.kind =
      JoltInstructionKind.ofInstr row.instruction) :
    circuitFlagValue flag row.instruction row.metadata =
      row.bytecodeRow.circuitFlagValue flag := by
  cases flag with
  | addOperands =>
      change addOperands row.instruction = row.instructionRow.kind.addOperands
      rw [kindEq, JoltInstructionKind.addOperands_ofInstr]
  | subtractOperands =>
      change subtractOperands row.instruction =
        row.instructionRow.kind.subtractOperands
      rw [kindEq, JoltInstructionKind.subtractOperands_ofInstr]
  | multiplyOperands =>
      change multiplyOperands row.instruction =
        row.instructionRow.kind.multiplyOperands
      rw [kindEq, JoltInstructionKind.multiplyOperands_ofInstr]
  | load =>
      change isLoad row.instruction = row.instructionRow.kind.isLoad
      rw [kindEq, JoltInstructionKind.isLoad_ofInstr]
  | store =>
      change isStore row.instruction = row.instructionRow.kind.isStore
      rw [kindEq, JoltInstructionKind.isStore_ofInstr]
  | jump =>
      change isJump row.instruction = row.instructionRow.kind.isJump
      rw [kindEq, JoltInstructionKind.isJump_ofInstr]
  | writeLookupOutputToRD =>
      change writesLookupOutput row.instruction =
        row.instructionRow.kind.writesLookupOutput
      rw [kindEq, JoltInstructionKind.writesLookupOutput_ofInstr]
  | virtualInstruction =>
      rfl
  | assert =>
      change isAssert row.instruction = row.instructionRow.kind.isAssert
      rw [kindEq, JoltInstructionKind.isAssert_ofInstr]
  | doNotUpdateUnexpandedPC =>
      change doNotUpdateUnexpandedPC row.instruction row.metadata =
        (row.instructionRow.kind.isNoop ||
            match row.metadata.virtualSequenceRemaining with
            | some (_ + 1) => true
            | _ => false)
      unfold doNotUpdateUnexpandedPC
      rw [kindEq, JoltInstructionKind.isNoop_ofInstr]
  | advice =>
      change adviceOperands row.instruction =
        row.instructionRow.kind.adviceOperands
      rw [kindEq, JoltInstructionKind.adviceOperands_ofInstr]
  | isCompressed =>
      rfl
  | isFirstInSequence =>
      rfl
  | isLastInSequence =>
      rfl

theorem instructionFlagValue_eq_bytecodeRow
    (row : JoltTraceRow) (flag : JoltInstructionFlag)
    (kindEq : row.instructionRow.kind =
      JoltInstructionKind.ofInstr row.instruction) :
    instructionFlagValue flag row.instruction =
      row.bytecodeRow.instructionFlagValue flag := by
  cases flag with
  | leftOperandIsPC =>
      change leftIsPC row.instruction = row.instructionRow.kind.leftIsPC
      rw [kindEq, JoltInstructionKind.leftIsPC_ofInstr]
  | rightOperandIsImm =>
      change rightOperandIsImmediate row.instruction =
        row.instructionRow.kind.rightOperandIsImmediate
      rw [kindEq, JoltInstructionKind.rightOperandIsImmediate_ofInstr]
  | leftOperandIsRs1Value =>
      change (lookupFirstSource row.instruction).isSome =
        row.instructionRow.kind.lookupFirstSourceIsSome
      rw [kindEq, JoltInstructionKind.lookupFirstSourceIsSome_ofInstr]
  | rightOperandIsRs2Value =>
      change (lookupSecondSource row.instruction).isSome =
        row.instructionRow.kind.lookupSecondSourceIsSome
      rw [kindEq, JoltInstructionKind.lookupSecondSourceIsSome_ofInstr]
  | branch =>
      change isBranch row.instruction = row.instructionRow.kind.isBranch
      rw [kindEq, JoltInstructionKind.isBranch_ofInstr]
  | isNoop =>
      change isNoop row.instruction = row.instructionRow.kind.isNoop
      rw [kindEq, JoltInstructionKind.isNoop_ofInstr]

theorem instructionRafFlagValue_eq_bytecodeRow
    (row : JoltTraceRow)
    (kindEq : row.instructionRow.kind =
      JoltInstructionKind.ofInstr row.instruction) :
    instructionRafFlagValue row.instruction =
      row.bytecodeRow.instructionRafFlagValue := by
  change
    instructionRafFlagValue row.instruction =
      (row.instructionRow.kind.addOperands ||
          row.instructionRow.kind.subtractOperands ||
          row.instructionRow.kind.multiplyOperands ||
          row.instructionRow.kind.adviceOperands)
  unfold instructionRafFlagValue
  rw [kindEq, JoltInstructionKind.addOperands_ofInstr,
    JoltInstructionKind.subtractOperands_ofInstr,
    JoltInstructionKind.multiplyOperands_ofInstr,
    JoltInstructionKind.adviceOperands_ofInstr]

theorem lookupTable_eq_bytecodeRow
    (row : JoltTraceRow)
    (kindEq : row.instructionRow.kind =
      JoltInstructionKind.ofInstr row.instruction) :
    lookupTable row.instruction = row.bytecodeRow.lookupTable := by
  change lookupTable row.instruction = row.instructionRow.kind.lookupTable
  rw [kindEq, JoltInstructionKind.lookupTable_ofInstr]

end HonestWitness

/-- Rust's canonical default row, used to pad the proof trace to `2 ^ logT`. -/
def JoltTraceRow.noOp : JoltTraceRow where
  instruction := .NoOp
  instructionRow := JoltInstructionRow.noOp
  metadata := {
    pc := 0
    unexpandedPC := 0
    virtualSequenceRemaining := none
    isFirstInSequence := false
    isCompressed := false
  }
  capturedState := .nonMemory {
    rs1Value := 0
    rs2Value := 0
    rdPreValue := 0
    rdWriteValue := 0
  }

namespace HonestWitness

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

/-- Rust's fixed seven-bit register domain: architectural registers occupy
addresses `0..31`, followed by virtual registers. -/
noncomputable def registerAtAddress
    (state : SailJoltState) (address : RegisterAddress) : U64 :=
  if address.val < 32 then
    sourceValue state (.xreg (.Regidx (BitVec.ofNat 5 address.val)))
  else
    sourceValue state (.vreg (BitVec.ofNat RegisterAddressBits address.val))

/-- Value of an optional normalized register operand in a Sail state. -/
noncomputable def registerAtOptionalAddress
    (state : SailJoltState) (address : Option RegisterAddress) : U64 :=
  match address with
  | some address => registerAtAddress state address
  | none => 0

def ramAccessAddress (row : JoltTraceRow) : Option U64 :=
  match JoltTraceRowClass.ofInstr row.instruction with
  | .load | .store => some row.ramAddress
  | .nonMemory => none

/-- The optional address used by Rust's RAM witness.  Rust returns `none` only
for address zero and rejects a nonzero address below `lowestMemoryAddress`;
this total Lean helper maps both cases to `none`.  The `ramAddress_eq_zero`
field of `JoltTraceRow.Valid` rules out the rejected nonzero case, while
`ramAddressBound` records the subsequent `address < ram_k` check. -/
def remappedRamAddressFromPublic
    {params : JoltWitnessParams}
    (publicInputs : JoltPublicInputs params)
    (row : JoltTraceRow) : Option Nat :=
  match ramAccessAddress row with
  | some address =>
      if address == 0 ||
          address.toNat < publicInputs.lowestMemoryAddress.toNat then
        none
      else
        some ((address.toNat - publicInputs.lowestMemoryAddress.toNat) / 8)
  | none => none

end HonestWitness

/-- Native producer contracts supplied with a proof-facing `JoltTraceRow`.
They combine tracer conversion facts with the memory-layout checks needed by
witness generation, and are stated before embedding values in the proof field. -/
structure JoltTraceRow.Valid
    {params : JoltWitnessParams}
    (publicInputs : JoltPublicInputs params)
    (row : JoltTraceRow) (before after : SailJoltState) : Prop where
  /-- The executable instruction and the fixed proof row name the same final
  Rust instruction. -/
  instructionKind_eq :
    row.instructionRow.kind = JoltInstructionKind.ofInstr row.instruction
  /-- Register selectors are the exact normalized Rust operands. -/
  instructionRegisterOperands_eq :
    HonestWitness.instructionRegisterOperandsMatch row
  /-- Static immediates agree whenever the executable instruction retains
  them; advice rows keep their distinct proof-facing immediate. -/
  instructionImmediate_eq : HonestWitness.instructionImmediateMatches row
  /-- `BytecodePCMapper::get_pc` always returns a table index. -/
  pcBound : row.metadata.pc < params.bytecodeK
  /-- The logical row is exactly the fixed bytecode entry selected by `pc`. -/
  bytecodeRow_eq : ∀ inBounds : row.metadata.pc < params.bytecodeK,
    publicInputs.bytecode ⟨row.metadata.pc, inBounds⟩ = row.bytecodeRow
  /-- Rust reserves bytecode index zero for the canonical no-op row. -/
  noOpPC : HonestWitness.isNoop row.instruction = true → row.metadata.pc = 0
  nonNoOpPCActive : HonestWitness.isNoop row.instruction = false →
    row.metadata.pc < publicInputs.bytecodeActiveLength
  /-- Rust stores this sequence counter as an `Option<u16>`. -/
  virtualSequenceRemainingBound : ∀ remaining,
    row.metadata.virtualSequenceRemaining = some remaining → remaining < 2 ^ 16
  firstSourceAddressValid : ∀ source,
    HonestWitness.firstSource row.instruction = some source →
      HonestWitness.sourceAddressValid source
  secondSourceAddressValid : ∀ source,
    HonestWitness.secondSource row.instruction = some source →
      HonestWitness.sourceAddressValid source
  destinationAddressValid : ∀ destination,
    HonestWitness.destination row.instruction = some destination →
      HonestWitness.destinationAddressValid destination
  rs1Value_eq :
    row.rs1Value = HonestWitness.registerAtOptionalAddress before
      row.instructionRow.operands.rs1
  rs2Value_eq :
    row.rs2Value = HonestWitness.registerAtOptionalAddress before
      row.instructionRow.operands.rs2
  rdPreValue_eq :
    row.rdPreValue = HonestWitness.registerAtOptionalAddress before
      row.instructionRow.operands.rd
  rdWriteValue_eq :
    row.rdWriteValue = HonestWitness.registerAtOptionalAddress after
      row.instructionRow.operands.rd
  effectiveAddress :
    (HonestWitness.isLoad row.instruction ||
      HonestWitness.isStore row.instruction) = true →
      (row.ramAddress.toNat : Int) =
        (row.rs1Value.toNat : Int) +
          row.instructionRow.operands.imm
  addInput_nonnegative :
    HonestWitness.addOperands row.instruction = true →
      0 ≤ ((HonestWitness.instructionInputs row).1.toNat : Int) +
        (HonestWitness.instructionInputs row).2.toInt
  assertionAccepted :
    HonestWitness.isAssert row.instruction = true →
      HonestWitness.lookupOutput row = 1
  /-- The native lookup query output is the selected table entry at the
  materialized 128-bit lookup address. -/
  lookupOutput_eq_table : ∀ table,
    HonestWitness.lookupTable row.instruction = some table →
      HonestWitness.lookupOutput row =
        JoltLookupTable.materializeEntry table
          (InstructionLookupAddress.ofBits
            (HonestWitness.lookupIndex row))
  /-- The native lookup index carries either one combined address or the two
  ordinary interleaved operands, according to `InstructionRafFlag`. -/
  lookupAddressOperands :
    let address := InstructionLookupAddress.ofBits
      (HonestWitness.lookupIndex row)
    let operands := HonestWitness.lookupOperands row
    if HonestWitness.instructionRafFlagValue row.instruction then
      operands.1 = 0 ∧ operands.2.toNat = address.val
    else
      operands.1 = address.leftOperand ∧
        operands.2.toNat = address.rightOperand.toNat
  firstInSequence_isVirtual :
    row.metadata.isFirstInSequence = true →
      HonestWitness.isVirtual row.metadata = true
  jumpLink :
    HonestWitness.isJump row.instruction = true →
      (row.rdWriteValue.toNat : Int) =
        (row.metadata.unexpandedPC.toNat : Int) + 4 -
          (if row.metadata.isCompressed then 2 else 0)
  ramAddressBound :
    ∀ address,
      HonestWitness.remappedRamAddressFromPublic publicInputs row = some address →
        address < params.ramK
  ramAddress_eq :
    ∀ address,
      HonestWitness.remappedRamAddressFromPublic publicInputs row = some address →
        row.ramAddress.toNat =
          publicInputs.lowestMemoryAddress.toNat + 8 * address
  ramAddress_eq_zero :
    HonestWitness.remappedRamAddressFromPublic publicInputs row = none →
      row.ramAddress = 0
  ramReadValue_eq :
    ∀ address,
      HonestWitness.remappedRamAddressFromPublic publicInputs row = some address →
        row.ramReadValue =
          HonestWitness.memoryWord before
            (publicInputs.lowestMemoryAddress.toNat + 8 * address)
  ramReadValue_eq_zero :
    HonestWitness.remappedRamAddressFromPublic publicInputs row = none →
      row.ramReadValue = 0
  ramWriteValue_eq_zero :
    HonestWitness.remappedRamAddressFromPublic publicInputs row = none →
      row.ramWriteValue = 0

/-- The native branch decision materialized by Rust for a row. -/
def JoltTraceRow.shouldBranch (row : JoltTraceRow) : Bool :=
  HonestWitness.isBranch row.instruction &&
    HonestWitness.lookupOutput row == 1

/-- The native jump decision for a row with an actual successor. -/
def JoltTracePair.shouldJump (current next : JoltTraceRow) : Bool :=
  HonestWitness.isJump current.instruction &&
    !(HonestWitness.isNoop next.instruction)

/-- Native ordering contracts for adjacent materialized Rust trace rows. -/
structure JoltTracePair.Valid (current next : JoltTraceRow) : Prop where
  jumpTarget :
    JoltTracePair.shouldJump current next = true →
      next.metadata.unexpandedPC = HonestWitness.lookupOutput current
  branchTarget :
    current.shouldBranch = true →
      (next.metadata.unexpandedPC.toNat : Int) =
        (current.metadata.unexpandedPC.toNat : Int) +
          current.instructionRow.operands.imm
  ordinaryTarget :
    current.shouldBranch = false →
    HonestWitness.isJump current.instruction = false →
      (next.metadata.unexpandedPC.toNat : Int) =
        (current.metadata.unexpandedPC.toNat : Int) + 4 -
          (if HonestWitness.doNotUpdateUnexpandedPC
              current.instruction current.metadata then 4 else 0) -
          (if current.metadata.isCompressed then 2 else 0)
  inlinePC :
    HonestWitness.isVirtual current.metadata = true →
    HonestWitness.isLastInSequence current.metadata = false →
      next.metadata.pc = current.metadata.pc + 1
  sequenceStart :
    HonestWitness.isVirtual next.metadata = true →
    next.metadata.isFirstInSequence = false →
      HonestWitness.doNotUpdateUnexpandedPC
        current.instruction current.metadata = true

/-- An executed trace together with the native materialization and ordering
facts guaranteed by Rust's tracer, bytecode preprocessing, and padding. -/
structure HonestTrace (params : JoltWitnessParams)
    extends ExecutionTrace params where
  metadataValid : metadata.Valid
  /-- Number of real tracer rows before the witness provider supplies default
  no-op rows. -/
  unpaddedLength : Nat
  /-- Exact `ProverConfig::derive` trace-padding policy. -/
  traceLengthFromUnpadded :
    params.traceLength = JoltWitnessParams.paddedTraceLength unpaddedLength
  unpaddedLengthBound : unpaddedLength ≤ params.traceLength
  /-- `TraceSource::next_row = none` is materialized as `TraceRow::default`. -/
  paddingRows : ∀ i : Fin params.traceLength,
    unpaddedLength ≤ i.val → rows i = JoltTraceRow.noOp
  rowValid : ∀ i : Fin params.traceLength,
    JoltTraceRow.Valid metadata.toJoltPublicInputs (rows i)
      (state (currentStateIndex i)) (state (nextStateIndex i))
  pairValid : ∀ (i j : Fin params.traceLength),
    HonestWitness.nextTraceIndex i = some j →
      JoltTracePair.Valid (rows i) (rows j)
  finalRow : ∀ i : Fin params.traceLength,
    HonestWitness.nextTraceIndex i = none → rows i = JoltTraceRow.noOp
  /-- Rust's bytecode entry boundary: cycle zero reads the compact public
  bytecode row derived from the ELF entry address. -/
  initialBytecodeIndex :
    (rows ⟨0, by simp [JoltWitnessParams.traceLength]⟩).metadata.pc =
      metadata.entryBytecodeIndex.val
  /-- Rust reconstructs `RegistersVal` from an all-zero register table. -/
  initialRegistersZero : ∀ address : RegisterAddress,
    HonestWitness.registerAtAddress
        (state ⟨0, Nat.zero_lt_succ params.traceLength⟩) address = 0
  /-- One proof row changes only its optional destination register. -/
  registerStateTransition : ∀ (i : Fin params.traceLength)
      (address : RegisterAddress),
    HonestWitness.registerAtAddress (state (nextStateIndex i)) address =
      match (rows i).instructionRow.operands.rd with
      | some destination =>
          if destination = address then
            (rows i).rdWriteValue
          else
            HonestWitness.registerAtAddress (state (currentStateIndex i)) address
      | none =>
          HonestWitness.registerAtAddress (state (currentStateIndex i)) address
  /-- Rust's dense initial RAM state is public program/input memory overlaid by
  the optional trusted and untrusted advice commitments. -/
  initialRamState : ∀ address : Fin params.ramK,
    HonestWitness.memoryWord
        (state ⟨0, Nat.zero_lt_succ params.traceLength⟩)
        (metadata.lowestMemoryAddress.toNat + 8 * address.val) =
      metadata.initialRamValue address
  /-- One row changes only its remapped RAM address, and the post-row value is
  exactly Rust's aliased `ram_write_value`. -/
  ramStateTransition : ∀ (i : Fin params.traceLength)
      (address : Fin params.ramK),
    HonestWitness.memoryWord
        (state (nextStateIndex i))
        (metadata.lowestMemoryAddress.toNat + 8 * address.val) =
      if HonestWitness.remappedRamAddressFromPublic
          metadata.toJoltPublicInputs (rows i) = some address.val then
        (rows i).ramWriteValue
      else
        HonestWitness.memoryWord
          (state (currentStateIndex i))
          (metadata.lowestMemoryAddress.toNat + 8 * address.val)
  ramOutputValid : ∀ address : Fin params.ramK,
    metadata.toJoltPublicInputs.ramOutputMask address = true →
      HonestWitness.memoryWord
          (state ⟨params.traceLength, Nat.lt_succ_self params.traceLength⟩)
          (metadata.lowestMemoryAddress.toNat + 8 * address.val) =
        metadata.toJoltPublicInputs.ramOutputValue address

def HonestTrace.instrList {params : JoltWitnessParams}
    (trace : HonestTrace params) : Column params.traceLength JoltISA.Instr :=
  trace.toExecutionTrace.instrList

def HonestTrace.rowMetadata {params : JoltWitnessParams}
    (trace : HonestTrace params) : Column params.traceLength JoltTraceRowMetadata :=
  trace.toExecutionTrace.rowMetadata

def HonestTrace.preState {params : JoltWitnessParams}
    (trace : HonestTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.toExecutionTrace.preState i

def HonestTrace.postState {params : JoltWitnessParams}
    (trace : HonestTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.toExecutionTrace.postState i

namespace HonestWitness

def nextMetadata {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (i : Fin params.traceLength) : Option JoltTraceRowMetadata :=
  (nextTraceIndex i).map trace.rowMetadata

def nextInstruction {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (i : Fin params.traceLength) : Option JoltISA.Instr :=
  (nextTraceIndex i).map trace.instrList

def finalState {params : JoltWitnessParams}
    (trace : HonestTrace params) : SailJoltState :=
  trace.state ⟨params.traceLength, Nat.lt_succ_self params.traceLength⟩

def remappedRamAddress
    {params : JoltWitnessParams}
    (trace : HonestTrace params)
    (row : JoltTraceRow) : Option Nat :=
  remappedRamAddressFromPublic trace.metadata.toJoltPublicInputs row

def ramReadValue (row : JoltTraceRow) : U64 :=
  row.ramReadValue

def ramWriteValue (row : JoltTraceRow) : U64 :=
  row.ramWriteValue

def ramIncrement (row : JoltTraceRow) : U128 :=
  if isStore row.instruction then
    BitVec.ofInt InstructionLookupAddressBits
      (((row.ramWriteValue.toNat : Int) - row.ramReadValue.toNat))
  else
    0

def oneHot {F : Type u} [Field F] (actual expected : Nat) : F :=
  fieldBool (actual == expected)

def productValue (row : JoltTraceRow) : Int :=
  let inputs := instructionInputs row
  (inputs.1.toNat : Int) * inputs.2.toInt

noncomputable def honest_witness
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) : JoltWitness params F where
  committed := fun polynomial =>
    match polynomial with
    | .rdInc => fun i =>
        fieldFromI128 (rdIncrement (trace.rows i))
    | .ramInc => fun i =>
        fieldFromI128 (ramIncrement (trace.rows i))
    | .instructionRa chunk => fun address i =>
        oneHot address.val
          ((params.instructionCommittedSelector chunk).chunk
            (lookupIndex (trace.rows i)).toNat).val
    | .bytecodeRa chunk => fun address i =>
        oneHot address.val
          ((params.bytecodeCommittedSelector chunk).chunk
            (trace.rowMetadata i).pc).val
    | .ramRa chunk => fun address i =>
        match remappedRamAddress trace (trace.rows i) with
        | some ramAddress =>
            oneHot address.val
              ((params.ramCommittedSelector chunk).chunk ramAddress).val
        | none => 0
    | .trustedAdvice _ => fun i =>
        fieldFromU64 (trace.metadata.trustedAdvice i)
    | .untrustedAdvice _ => fun i =>
        fieldFromU64 (trace.metadata.untrustedAdvice i)

  virtual := fun polynomial =>
    match polynomial with
    | .pc => fun i => ((trace.rowMetadata i).pc : F)
    | .unexpandedPC => fun i =>
        fieldFromU64 (trace.rowMetadata i).unexpandedPC
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
      | none => true
    | .nextIsVirtual => fun i =>
        fieldBool <| match nextMetadata trace i with
        | some metadata => isVirtual metadata
        | none => false
    | .nextIsFirstInSequence => fun i =>
        fieldBool <| match nextMetadata trace i with
        | some metadata => metadata.isFirstInSequence
        | none => false
    | .leftLookupOperand => fun i =>
        fieldFromU64 (lookupOperands (trace.rows i)).1
    | .rightLookupOperand => fun i =>
        fieldFromU128 (lookupOperands (trace.rows i)).2
    | .leftInstructionInput => fun i =>
        fieldFromU64 (instructionInputs (trace.rows i)).1
    | .rightInstructionInput => fun i =>
        fieldFromI128 (instructionInputs (trace.rows i)).2
    | .product => fun i =>
        fieldFromInt (productValue (trace.rows i))
    | .shouldJump => fun i =>
        fieldBool <| isJump (trace.instrList i) &&
          match nextInstruction trace i with
          | some instruction => !(isNoop instruction)
          | none => true
    | .shouldBranch => fun i =>
        fieldBool <| isBranch (trace.instrList i) &&
          lookupOutput (trace.rows i) == 1
    | .imm => fun i =>
        fieldFromInt (trace.rows i).instructionRow.operands.imm
    | .rs1Value => fun i =>
        fieldFromU64 (trace.rows i).rs1Value
    | .rs2Value => fun i =>
        fieldFromU64 (trace.rows i).rs2Value
    | .rdWriteValue => fun i =>
        fieldFromU64 (trace.rows i).rdWriteValue
    | .lookupOutput => fun i =>
        fieldFromU64 (lookupOutput (trace.rows i))
    | .instructionRafFlag => fun i =>
        fieldBool (instructionRafFlagValue (trace.instrList i))
    | .rs1Ra => fun address i =>
        registerAddressIndicator
          (trace.rows i).instructionRow.operands.rs1 address
    | .rs2Ra => fun address i =>
        registerAddressIndicator
          (trace.rows i).instructionRow.operands.rs2 address
    | .rdWa => fun address i =>
        registerAddressIndicator
          (trace.rows i).instructionRow.operands.rd address
    | .instructionRa chunk => fun address i =>
        oneHot address.val
          ((params.instructionVirtualSelector chunk).chunk
            (lookupIndex (trace.rows i)).toNat).val
    | .registersVal => fun address i =>
        fieldFromU64 (registerAtAddress (trace.preState i) address)
    | .ramAddress => fun i =>
        fieldFromU64 (trace.rows i).ramAddress
    | .ramRa => fun address i =>
        match remappedRamAddress trace (trace.rows i) with
        | some ramAddress => oneHot address.val ramAddress
        | none => 0
    | .ramReadValue => fun i =>
        fieldFromU64 (trace.rows i).ramReadValue
    | .ramWriteValue => fun i =>
        fieldFromU64 (trace.rows i).ramWriteValue
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
        fieldBool <| match ramAccessAddress (trace.rows i) with
        | some address => address != 0
        | none => false
    | .opFlag flag => fun i =>
        fieldBool
          (circuitFlagValue flag (trace.instrList i) (trace.rowMetadata i))
    | .instructionFlag flag => fun i =>
        fieldBool (instructionFlagValue flag (trace.instrList i))
    | .lookupTableFlag table => fun i =>
        fieldBool (lookupTable (trace.instrList i) == some table)

end HonestWitness

export HonestWitness (honest_witness)

end JoltConstraints
