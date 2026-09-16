import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace JoltMetadata

-- Rust: crates/jolt-riscv/src/instructions/{i,m,virt,assert}/*.rs (instruction flags).
-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction.
def instructionFlag (instruction : JoltISA.Instr) (flag : InstructionFlags) : Bool :=
  match flag with
  | .LeftOperandIsPC =>
      match instruction with
      | .AUIPC .. | .JAL .. => true
      | _ => false
  | .RightOperandIsImm =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .LUI .. | .AUIPC .. | .JAL .. | .JALR .. | .VirtualMULI .. | .VirtualMULIW ..
      | .VirtualPow2I .. | .VirtualPow2IW .. | .VirtualShiftRightBitmaskI ..
      | .VirtualSRLI .. | .VirtualSRAI .. | .VirtualSRLIW .. | .VirtualSRAIW ..
      | .VirtualROTRI .. | .VirtualROTRIW .. | .VirtualAlignAddr .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualMovsign ..
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment .. => true
      | _ => false
  | .LeftOperandIsRs1Value =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .JALR .. | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. | .ADD ..
      | .ADDW .. | .SUB .. | .SUBW .. | .MUL .. | .MULW .. | .MULHU .. | .ANDN ..
      | .VirtualMULI .. | .VirtualMULIW .. | .VirtualPow2 .. | .VirtualPow2W ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskW .. | .VirtualSRLI ..
      | .VirtualSRAI .. | .VirtualSRLIW .. | .VirtualSRAIW .. | .VirtualSRL ..
      | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW .. | .VirtualROTRI ..
      | .VirtualROTRIW .. | .VirtualRev8W .. | .VirtualXORROT32 .. | .VirtualXORROT24 ..
      | .VirtualXORROT16 .. | .VirtualXORROT63 .. | .VirtualXORROTW16 ..
      | .VirtualXORROTW12 .. | .VirtualXORROTW8 .. | .VirtualXORROTW7 ..
      | .VirtualXORROTW22 .. | .VirtualXORROTW19 .. | .VirtualXORROTW6 .. | .OR .. | .XOR ..
      | .AND .. | .SLT .. | .SLTU .. | .VirtualAlignAddr .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualPext ..
      | .VirtualPextSigned .. | .VirtualShiftDataB .. | .VirtualShiftDataH ..
      | .VirtualShiftDataW .. | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualMovsign .. | .VirtualAssertHalfwordAlignment ..
      | .VirtualAssertWordAlignment .. | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualNegateIf .. | .VirtualAssertValidUnsignedRemainder ..
      | .VirtualAssertMulUNoOverflow .. | .VirtualAssertLTE .. => true
      | _ => false
  | .RightOperandIsRs2Value =>
      match instruction with
      | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. | .ADD .. | .ADDW ..
      | .SUB .. | .SUBW .. | .MUL .. | .MULW .. | .MULHU .. | .ANDN .. | .VirtualSRL ..
      | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW .. | .VirtualXORROT32 ..
      | .VirtualXORROT24 .. | .VirtualXORROT16 .. | .VirtualXORROT63 ..
      | .VirtualXORROTW16 .. | .VirtualXORROTW12 .. | .VirtualXORROTW8 ..
      | .VirtualXORROTW7 .. | .VirtualXORROTW22 .. | .VirtualXORROTW19 ..
      | .VirtualXORROTW6 .. | .OR .. | .XOR .. | .AND .. | .SLT .. | .SLTU ..
      | .VirtualPext .. | .VirtualPextSigned .. | .VirtualShiftDataB ..
      | .VirtualShiftDataH .. | .VirtualShiftDataW .. | .VirtualAssertEQ ..
      | .VirtualAssertValidDiv0 .. | .VirtualNegateIf ..
      | .VirtualAssertValidUnsignedRemainder .. | .VirtualAssertMulUNoOverflow ..
      | .VirtualAssertLTE .. => true
      | _ => false
  | .Branch =>
      match instruction with
      | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => true
      | _ => false
  | .IsNoop => false

-- Rust: crates/jolt-riscv/src/instructions/{i,m,virt,assert}/*.rs (circuit flags).
-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction.
def opcodeFlag (instruction : JoltISA.Instr) (flag : CircuitFlags) : Bool :=
  match flag with
  | .AddOperands =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .LUI .. | .AUIPC .. | .JAL .. | .JALR .. | .ADD .. | .ADDW ..
      | .VirtualPow2 .. | .VirtualPow2W .. | .VirtualPow2I .. | .VirtualPow2IW ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI ..
      | .VirtualShiftRightBitmaskW .. | .VirtualRev8W .. | .VirtualAlignAddr ..
      | .VirtualWindowMaskB .. | .VirtualWindowMaskH .. | .VirtualWindowMaskW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment .. => true
      | _ => false
  | .SubtractOperands =>
      match instruction with
      | .SUB .. | .SUBW .. => true
      | _ => false
  | .MultiplyOperands =>
      match instruction with
      | .MUL .. | .MULW .. | .MULHU .. | .VirtualMULI .. | .VirtualMULIW ..
      | .VirtualAssertMulUNoOverflow .. => true
      | _ => false
  | .Load =>
      match instruction with
      | .LD .. => true
      | _ => false
  | .Store =>
      match instruction with
      | .SD .. => true
      | _ => false
  | .Jump =>
      match instruction with
      | .JAL .. | .JALR .. => true
      | _ => false
  | .WriteLookupOutputToRD =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .LUI .. | .AUIPC .. | .ADD .. | .ADDW .. | .SUB .. | .SUBW .. | .MUL .. | .MULW ..
      | .MULHU .. | .ANDN .. | .VirtualMULI .. | .VirtualMULIW .. | .VirtualPow2 ..
      | .VirtualPow2W .. | .VirtualPow2I .. | .VirtualPow2IW ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI ..
      | .VirtualShiftRightBitmaskW .. | .VirtualSRLI .. | .VirtualSRAI .. | .VirtualSRLIW ..
      | .VirtualSRAIW .. | .VirtualSRL .. | .VirtualSRA .. | .VirtualSRLW ..
      | .VirtualSRAW .. | .VirtualROTRI .. | .VirtualROTRIW .. | .VirtualRev8W ..
      | .VirtualXORROT32 .. | .VirtualXORROT24 .. | .VirtualXORROT16 ..
      | .VirtualXORROT63 .. | .VirtualXORROTW16 .. | .VirtualXORROTW12 ..
      | .VirtualXORROTW8 .. | .VirtualXORROTW7 .. | .VirtualXORROTW22 ..
      | .VirtualXORROTW19 .. | .VirtualXORROTW6 .. | .OR .. | .XOR .. | .AND .. | .SLT ..
      | .SLTU .. | .VirtualAlignAddr .. | .VirtualWindowMaskB .. | .VirtualWindowMaskH ..
      | .VirtualWindowMaskW .. | .VirtualPext .. | .VirtualPextSigned ..
      | .VirtualShiftDataB .. | .VirtualShiftDataH .. | .VirtualShiftDataW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord .. | .VirtualMovsign ..
      | .VirtualAdvice .. | .VirtualAdviceLoad .. | .VirtualAdviceLen ..
      | .VirtualNegateIf .. => true
      | _ => false
  | .VirtualInstruction => false
  | .Assert =>
      match instruction with
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment ..
      | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualAssertValidUnsignedRemainder .. | .VirtualAssertMulUNoOverflow ..
      | .VirtualAssertLTE .. => true
      | _ => false
  | .DoNotUpdateUnexpandedPC => false
  | .Advice =>
      match instruction with
      | .VirtualAdvice .. | .VirtualAdviceLoad .. | .VirtualAdviceLen .. => true
      | _ => false
  | .IsCompressed => false
  | .IsFirstInSequence => false
  | .IsLastInSequence => false

-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction (row-dependent circuit flags).
def circuitFlag (row : JoltProgramRow) (flag : CircuitFlags) : Bool :=
  match flag with
  | .VirtualInstruction => row.virtualSequenceRemaining.isSome
  | .IsLastInSequence => row.virtualSequenceRemaining == some 0
  | .DoNotUpdateUnexpandedPC => row.virtualSequenceRemaining.getD 0 != 0
  | .IsCompressed => row.isCompressed
  | .IsFirstInSequence => row.isFirstInSequence
  | _ => opcodeFlag row.instruction flag

-- Rust: crates/jolt-lookup-tables/src/instructions/{riscv,virt}/::impl_lookup_table.
def lookupTable (instruction : JoltISA.Instr) : Option LookupTableKind :=
  match instruction with
  | .ADDI .. | .LUI .. | .AUIPC .. | .JAL .. | .ADD .. | .SUB .. | .MUL ..
  | .VirtualMULI .. | .VirtualAdvice .. | .VirtualAdviceLoad ..
  | .VirtualAdviceLen .. => some .RangeCheck
  | .ADDIW .. | .ADDW .. | .SUBW .. | .MULW .. | .VirtualMULIW ..
  | .VirtualSignExtendWord .. => some .SignExtendWord
  | .ANDI .. | .AND .. => some .And
  | .ORI .. | .OR .. => some .Or
  | .XORI .. | .XOR .. => some .Xor
  | .SLTI .. | .BLT .. | .SLT .. => some .SignedLessThan
  | .SLTIU .. | .BLTU .. | .SLTU .. => some .UnsignedLessThan
  | .JALR .. => some .RangeCheckAligned
  | .BEQ .. | .VirtualAssertEQ .. => some .Equal
  | .BNE .. => some .NotEqual
  | .BGE .. => some .SignedGreaterThanEqual
  | .BGEU .. => some .UnsignedGreaterThanEqual
  | .FENCE .. | .LD .. | .SD .. | .VirtualHostIO .. => none
  | .MULHU .. => some .UpperWord
  | .ANDN .. => some .Andn
  | .VirtualPow2 .. | .VirtualPow2I .. => some .Pow2
  | .VirtualPow2W .. | .VirtualPow2IW .. => some .Pow2W
  | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI .. => some .ShiftRightBitmask
  | .VirtualShiftRightBitmaskW .. => some .ShiftRightBitmaskW
  | .VirtualSRLI .. | .VirtualSRL .. => some .VirtualSRL
  | .VirtualSRAI .. | .VirtualSRA .. => some .VirtualSRA
  | .VirtualSRLIW .. | .VirtualSRLW .. => some .VirtualSRLW
  | .VirtualSRAIW .. | .VirtualSRAW .. => some .VirtualSRAW
  | .VirtualROTRI .. => some .VirtualROTR
  | .VirtualROTRIW .. => some .VirtualROTRW
  | .VirtualRev8W .. => some .VirtualRev8W
  | .VirtualXORROT32 .. => some .VirtualXORROT32
  | .VirtualXORROT24 .. => some .VirtualXORROT24
  | .VirtualXORROT16 .. => some .VirtualXORROT16
  | .VirtualXORROT63 .. => some .VirtualXORROT63
  | .VirtualXORROTW16 .. => some .VirtualXORROTW16
  | .VirtualXORROTW12 .. => some .VirtualXORROTW12
  | .VirtualXORROTW8 .. => some .VirtualXORROTW8
  | .VirtualXORROTW7 .. => some .VirtualXORROTW7
  | .VirtualXORROTW22 .. => some .VirtualXORROTW22
  | .VirtualXORROTW19 .. => some .VirtualXORROTW19
  | .VirtualXORROTW6 .. => some .VirtualXORROTW6
  | .VirtualAlignAddr .. => some .AlignAddr
  | .VirtualWindowMaskB .. => some .WindowMaskB
  | .VirtualWindowMaskH .. => some .WindowMaskH
  | .VirtualWindowMaskW .. => some .WindowMaskW
  | .VirtualPext .. => some .Pext
  | .VirtualPextSigned .. => some .PextSigned
  | .VirtualShiftDataB .. => some .ShiftDataB
  | .VirtualShiftDataH .. => some .ShiftDataH
  | .VirtualShiftDataW .. => some .ShiftDataW
  | .VirtualZeroExtendWord .. => some .LowerHalfWord
  | .VirtualMovsign .. => some .SignMask
  | .VirtualAssertHalfwordAlignment .. => some .HalfwordAlignment
  | .VirtualAssertWordAlignment .. => some .WordAlignment
  | .VirtualAssertValidDiv0 .. => some .ValidDiv0
  | .VirtualNegateIf .. => some .VirtualNegateIf
  | .VirtualAssertValidUnsignedRemainder .. => some .ValidUnsignedRemainder
  | .VirtualAssertMulUNoOverflow .. => some .MulUNoOverflow
  | .VirtualAssertLTE .. => some .UnsignedLessThanEqual

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::LookupTableFlag::extract_indexed.
def lookupTableFlag (instruction : JoltISA.Instr) (table : LookupTableKind) : Bool :=
  lookupTable instruction == some table

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionRafFlag::extract.
def instructionRafFlag (instruction : JoltISA.Instr) : Bool :=
  opcodeFlag instruction .AddOperands || opcodeFlag instruction .SubtractOperands ||
    opcodeFlag instruction .MultiplyOperands || opcodeFlag instruction .Advice

end JoltMetadata
