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

noncomputable def programCounter (state : SailJoltState) : BitVec Xlen :=
  match (Sail.readReg Register.PC) state.sail with
  | .ok value _ => value
  | .error _ _ => 0

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

def lowImmediate : JoltISA.Instr → Option U128
  | .ADDI _ _ immediate
  | .ANDI _ _ immediate
  | .ORI _ _ immediate
  | .XORI _ _ immediate
  | .SLTI _ _ immediate
  | .SLTIU _ _ immediate
  | .JALR _ _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits
        (sign_extend (m := Xlen) immediate).toNat)
  | .LUI _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits immediate.toNat)
  | .AUIPC _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits
        (sign_extend (m := Xlen) (immediate +++ (0 : BitVec 12))).toNat)
  | .JAL _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits
        (sign_extend (m := Xlen) immediate).toNat)
  | .VirtualMULI _ _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits immediate.toNat)
  | .VirtualPow2I _ immediate
  | .VirtualPow2IW _ immediate
  | .VirtualShiftRightBitmaskI _ immediate
  | .VirtualSRLI _ _ immediate
  | .VirtualSRAI _ _ immediate
  | .VirtualROTRI _ _ immediate
  | .VirtualROTRIW _ _ immediate =>
      some (BitVec.ofNat InstructionLookupAddressBits immediate)
  | .VirtualMovsign _ _ => some 0
  | .VirtualAssertHalfwordAlignment _ immediate _
  | .VirtualAssertWordAlignment _ immediate _ =>
      some (BitVec.ofInt InstructionLookupAddressBits immediate.toInt)
  | _ => none

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

def usesANDTable : JoltISA.Instr → Bool
  | .ANDI _ _ _ | .AND _ _ _ => true
  | _ => false

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
    (instruction : JoltISA.Instr) (before : SailJoltState) : U64 × U128 :=
  let left :=
    if leftIsPC instruction then
      programCounter before
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
    (before after : SailJoltState) : U64 × U128 :=
  let inputs := instructionInputs instruction before
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
    (before after : SailJoltState) : U128 :=
  let operands := lookupOperands instruction before after
  if addOperands instruction || subtractOperands instruction ||
      multiplyOperands instruction || adviceOperands instruction then
    operands.2
  else
    interleave operands.1 (low64 operands.2)

def boolU64 (value : Bool) : U64 :=
  if value then 1 else 0

noncomputable def lookupOutput
    (instruction : JoltISA.Instr)
    (before after : SailJoltState) : U64 :=
  if writesLookupOutput instruction then
    destinationRegisterValue after instruction
  else
    let inputs := instructionInputs instruction before
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
        boolU64 ((lookupOperands instruction before after).2.toNat % 2 == 0)
    | .VirtualAssertWordAlignment _ _ _ =>
        boolU64 ((lookupOperands instruction before after).2.toNat % 4 == 0)
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

noncomputable def honest_witness {T : Nat} {F : Type u} [Field F]
    (trace : HonestTrace T) : JoltWitness T F where
  committed := fun polynomial =>
    match polynomial with
    | .rdInc => fun i =>
        fieldFromI128
          (rdIncrement (trace.instrList i) (trace.preState i) (trace.postState i))
    | .instructionRa => fun address i =>
        fieldBool (address ==
          (lookupIndex
            (trace.instrList i) (trace.preState i) (trace.postState i)).toFin)

  virtual := fun polynomial =>
    match polynomial with
    | .leftLookupOperand => fun i =>
        fieldFromU64
          (lookupOperands
            (trace.instrList i) (trace.preState i) (trace.postState i)).1
    | .rightLookupOperand => fun i =>
        fieldFromU128
          (lookupOperands
            (trace.instrList i) (trace.preState i) (trace.postState i)).2
    | .leftInstructionInput => fun i =>
        fieldFromU64
          (instructionInputs (trace.instrList i) (trace.preState i)).1
    | .rightInstructionInput => fun i =>
        fieldFromI128
          (instructionInputs (trace.instrList i) (trace.preState i)).2
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
          (lookupOutput (trace.instrList i) (trace.preState i) (trace.postState i))
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
    | .opFlag flag => fun i =>
        fieldBool <| match flag with
        | .addOperands => addOperands (trace.instrList i)
        | .subtractOperands => subtractOperands (trace.instrList i)
        | .multiplyOperands => multiplyOperands (trace.instrList i)
        | .advice => adviceOperands (trace.instrList i)
        | .writeLookupOutputToRD => writesLookupOutput (trace.instrList i)
    | .instructionFlag .leftOperandIsRs1Value => fun i =>
        fieldBool (lookupFirstSource (trace.instrList i)).isSome
    | .instructionFlag .rightOperandIsRs2Value => fun i =>
        fieldBool (lookupSecondSource (trace.instrList i)).isSome
    | .instructionFlag .rightOperandIsImm => fun i =>
        fieldBool (lowImmediate (trace.instrList i)).isSome
    | .lookupTableFlag .AND => fun i =>
        fieldBool (usesANDTable (trace.instrList i))

end HonestWitness

export HonestWitness (honest_witness)

end JoltConstraints
