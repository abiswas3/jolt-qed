import JoltConstraints.witness

/-!
# Fixed Jolt lookup-table entries

This file is the discrete, finite-array counterpart of Rust's
`jolt-lookup-tables` crate.  `JoltLookupTable.materializeEntry` mirrors
`LookupTableKind::<64>::materialize_entry : u128 → u64` for every base-mode
table.  It does not model the optimized multilinear-extension evaluators used
by the Rust verifier.

Two-input lookup addresses interleave the left operand in odd-numbered bit
positions and the right operand in even-numbered positions.  Combined-operand
tables instead interpret the complete 128-bit address directly.
-/

namespace JoltConstraints

open Sail PreSail LeanRV64D.Functions

namespace InstructionLookupAddress

/-- Convert the bounded finite address to its exact 128-bit representation. -/
def toBits (address : InstructionLookupAddress) :
    BitVec InstructionLookupAddressBits :=
  BitVec.ofNat InstructionLookupAddressBits address.val

/-- Convert a 128-bit address to the bounded finite address domain. -/
def ofBits (address : BitVec InstructionLookupAddressBits) :
    InstructionLookupAddress :=
  address.toFin

private def bitValue (value bit : Nat) : Nat :=
  if value.testBit bit then 1 else 0

/-- Extract one of the two 64-bit operands from Rust's interleaved address.
Offset `1` selects the left/odd positions; offset `0` selects the right/even
positions. -/
private def uninterleaveNat (offset : Nat)
    (address : InstructionLookupAddress) : Nat :=
  (List.range Xlen).foldl
    (fun operand bit =>
      operand + bitValue address.val (2 * bit + offset) * 2 ^ bit)
    0

/-- Recover the left operand occupying odd-numbered address bits. -/
def leftOperand (address : InstructionLookupAddress) : BitVec Xlen :=
  BitVec.ofNat Xlen (uninterleaveNat 1 address)

/-- Recover the right operand occupying even-numbered address bits. -/
def rightOperand (address : InstructionLookupAddress) : BitVec Xlen :=
  BitVec.ofNat Xlen (uninterleaveNat 0 address)

/-- Rust's two-operand lookup-address interleaving. -/
def interleaveBits (left right : BitVec Xlen) :
    BitVec InstructionLookupAddressBits :=
  BitVec.ofNat InstructionLookupAddressBits <|
    (List.range Xlen).foldl
      (fun address bit =>
        address
          + bitValue left.toNat bit * 2 ^ (2 * bit + 1)
          + bitValue right.toNat bit * 2 ^ (2 * bit))
      0

def interleave (left right : BitVec Xlen) : InstructionLookupAddress :=
  ofBits (interleaveBits left right)

/-- Low 64 bits of a combined lookup address. -/
def lowWord (address : InstructionLookupAddress) : BitVec Xlen :=
  BitVec.ofNat Xlen address.val

/-- High 64 bits of a combined lookup address. -/
def highWord (address : InstructionLookupAddress) : BitVec Xlen :=
  BitVec.ofNat Xlen (address.val / 2 ^ Xlen)

end InstructionLookupAddress

namespace JoltLookupTable

private def boolWord (value : Bool) : BitVec Xlen :=
  if value then 1 else 0

private def bitValue (value bit : Nat) : Nat :=
  if value.testBit bit then 1 else 0

/-- State for Rust's full-domain `VirtualSRL` materialization formula. -/
private def virtualSrlNat (left right : BitVec Xlen) : Nat :=
  (List.range Xlen).foldl
    (fun entry offset =>
      let bit := Xlen - 1 - offset
      let x := bitValue left.toNat bit
      let y := bitValue right.toNat bit
      entry * (1 + y) + x * y)
    0

private structure SraState where
  entry : Nat
  signExtension : Nat

/-- State for Rust's full-domain `VirtualSRA` materialization formula. -/
private def virtualSraNat (left right : BitVec Xlen) : Nat :=
  let result :=
    (List.range Xlen).foldl
      (fun state offset =>
        let bit := Xlen - 1 - offset
        let x := bitValue left.toNat bit
        let y := bitValue right.toNat bit
        { entry := state.entry * (1 + y) + x * y
          signExtension := state.signExtension +
            (if offset = 0 then 0 else 2 ^ offset * (1 - y)) })
      ({ entry := 0, signExtension := 0 } : SraState)
  result.entry + bitValue left.toNat (Xlen - 1) * result.signExtension

private structure RotState where
  productOnePlusY : Nat
  firstSum : Nat
  secondSum : Nat

/-- State for Rust's full-domain `VirtualROTR` materialization formula. -/
private def virtualRotrNat (left right : BitVec Xlen) : Nat :=
  let result :=
    (List.range Xlen).foldl
      (fun state offset =>
        let bit := Xlen - 1 - offset
        let x := bitValue left.toNat bit
        let y := bitValue right.toNat bit
        { productOnePlusY := state.productOnePlusY * (1 + y)
          firstSum := state.firstSum * (1 + y) + x * y
          secondSum := state.secondSum +
            x * (1 - y) * state.productOnePlusY * 2 ^ bit })
      ({ productOnePlusY := 1, firstSum := 0, secondSum := 0 } : RotState)
  result.firstSum + result.secondSum

/-- State for Rust's full-domain `VirtualROTRW` materialization formula. -/
private def virtualRotrWNat (left right : BitVec Xlen) : Nat :=
  let half := Xlen / 2
  let result :=
    (List.range half).foldl
      (fun state offset =>
        let bit := half - 1 - offset
        let x := bitValue left.toNat bit
        let y := bitValue right.toNat bit
        { productOnePlusY := state.productOnePlusY * (1 + y)
          firstSum := state.firstSum * (1 + y) + x * y
          secondSum := state.secondSum +
            x * (1 - y) * state.productOnePlusY * 2 ^ bit })
      ({ productOnePlusY := 1, firstSum := 0, secondSum := 0 } : RotState)
  result.firstSum + result.secondSum

/-- Rust's `LookupTableKind::<64>::materialize_entry`, exhaustively mirrored
over the closed Lean table identifier. -/
def materializeEntry (table : JoltLookupTable)
    (address : InstructionLookupAddress) : BitVec Xlen :=
  let left := address.leftOperand
  let right := address.rightOperand
  let low := address.lowWord
  match table with
  | .RangeCheck => low
  | .RangeCheckAligned =>
      BitVec.ofNat Xlen (address.val - address.val % 2)
  | .AND => left &&& right
  | .ANDN => left &&& (~~~ right)
  | .OR => left ||| right
  | .XOR => left ^^^ right
  | .Equal => boolWord (left == right)
  | .SignedGreaterThanEqual => boolWord (left.toInt ≥ right.toInt)
  | .UnsignedGreaterThanEqual => boolWord (left.toNat ≥ right.toNat)
  | .NotEqual => boolWord (left != right)
  | .SignedLessThan => boolWord (left.toInt < right.toInt)
  | .UnsignedLessThan => boolWord (left.toNat < right.toNat)
  | .SignMask =>
      if address.val.testBit (InstructionLookupAddressBits - 1) then
        -1
      else
        0
  | .UpperWord => address.highWord
  | .UnsignedLessThanEqual => boolWord (left.toNat ≤ right.toNat)
  | .ValidUnsignedRemainder =>
      boolWord (right == 0 || left.toNat < right.toNat)
  | .ValidDiv0 =>
      if left == 0 then boolWord (right == (-1 : BitVec Xlen)) else 1
  | .HalfwordAlignment => boolWord (address.val % 2 = 0)
  | .WordAlignment => boolWord (address.val % 4 = 0)
  | .LowerHalfWord => BitVec.ofNat Xlen (address.val % 2 ^ (Xlen / 2))
  | .SignExtendHalfWord =>
      (BitVec.ofNat (Xlen / 2) address.val).signExtend Xlen
  | .Pow2 => BitVec.ofNat Xlen (2 ^ (address.val % Xlen))
  | .Pow2W => BitVec.ofNat Xlen (2 ^ (address.val % (Xlen / 2)))
  | .ShiftRightBitmask =>
      let shift := address.val % Xlen
      BitVec.ofNat Xlen ((2 ^ (Xlen - shift) - 1) * 2 ^ shift)
  | .VirtualRev8W => jolt_virtual_rev8w_value low
  | .VirtualSRL => BitVec.ofNat Xlen (virtualSrlNat left right)
  | .VirtualSRA => BitVec.ofNat Xlen (virtualSraNat left right)
  | .VirtualROTR => BitVec.ofNat Xlen (virtualRotrNat left right)
  | .VirtualROTRW => BitVec.ofNat Xlen (virtualRotrWNat left right)
  | .VirtualChangeDivisor => change_divisor_value left right
  | .VirtualChangeDivisorW => change_divisor_w_value left right
  | .MulUNoOverflow => boolWord (address.highWord == 0)
  | .VirtualXORROT32 => jolt_virtual_xorrot_value 32 left right
  | .VirtualXORROT24 => jolt_virtual_xorrot_value 24 left right
  | .VirtualXORROT16 => jolt_virtual_xorrot_value 16 left right
  | .VirtualXORROT63 => jolt_virtual_xorrot_value 63 left right
  | .VirtualXORROTW16 => jolt_virtual_xorrotw_value 16 left right
  | .VirtualXORROTW12 => jolt_virtual_xorrotw_value 12 left right
  | .VirtualXORROTW8 => jolt_virtual_xorrotw_value 8 left right
  | .VirtualXORROTW7 => jolt_virtual_xorrotw_value 7 left right

end JoltLookupTable

/-! Small executable checks pin the two easy-to-reverse conventions and the
bespoke full-domain formulas.  These are regression checks against the Rust
examples/formulas, not a claimed cross-language equivalence theorem. -/

section MaterializationChecks

private def interleavedAddress (left right : Nat) : InstructionLookupAddress :=
  InstructionLookupAddress.interleave
    (BitVec.ofNat Xlen left) (BitVec.ofNat Xlen right)

private def combinedAddress (value : Nat) : InstructionLookupAddress :=
  InstructionLookupAddress.ofBits
    (BitVec.ofNat InstructionLookupAddressBits value)

example : (interleavedAddress 1 2).val = 6 := by native_decide

example :
    (interleavedAddress 1 2).leftOperand.toNat = 1 ∧
      (interleavedAddress 1 2).rightOperand.toNat = 2 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .AND
      (interleavedAddress 0xf0 0xcc)).toNat = 0xc0 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .ValidDiv0
      (interleavedAddress 0 0xffffffffffffffff)).toNat = 1 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .ValidDiv0
      (interleavedAddress 0 0)).toNat = 0 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .ShiftRightBitmask
      (combinedAddress 1)).toNat = 0xfffffffffffffffe := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualSRL
      (interleavedAddress 8 0xfffffffffffffffe)).toNat = 4 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualSRA
      (interleavedAddress 0x8000000000000000 0xfffffffffffffffe)).toNat =
        0xc000000000000000 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualROTR
      (interleavedAddress 1 0xfffffffffffffffe)).toNat =
        0x8000000000000000 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualROTRW
      (interleavedAddress 1 0xfffffffe)).toNat = 0x80000000 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualChangeDivisor
      (interleavedAddress 0x8000000000000000 0xffffffffffffffff)).toNat = 1 := by
  native_decide

example :
    (JoltLookupTable.materializeEntry .VirtualChangeDivisorW
      (interleavedAddress 0x80000000 0xffffffff)).toNat = 1 := by
  native_decide

end MaterializationChecks

end JoltConstraints
