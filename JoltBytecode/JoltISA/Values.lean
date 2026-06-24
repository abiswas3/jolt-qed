import JoltBytecode.JoltISA.Core
import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# Semantic value helpers

Pure value-level functions used by `JoltISA/Semantics.lean` to express the
result a single Jolt instruction writes to its destination register, plus the
shared Sail-side reference definitions used by instruction-equivalence proofs.

Contents:
* `ctz` — count trailing zeros, used by the virtual shift family.
* `Riscv.*` — Sail-equivalent pure reference functions for shift/multiply/
  bitwise ops, used in math-bridge lemmas.
* `jolt_*_value` — Jolt-side value functions consumed by `execInstr`.

Proof-side characterisations of these helpers live in
`InstructionEquivalence/ValueLemmas.lean`.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Count trailing zeros
-- ============================================================================

/-- Count trailing zeros of a natural number. Returns 0 for input 0. -/
def ctz (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 1 then 0
  else 1 + ctz (n / 2)
termination_by n

-- ============================================================================
-- Riscv pure-function reference definitions (Sail-equivalent abstractions)
-- ============================================================================

namespace Riscv

variable {w : Nat}

def mul (x y : BitVec w) : BitVec w := x * y
def slli (x : BitVec w) (shamt : Nat) : BitVec w := x <<< shamt
def ori (x imm : BitVec w) : BitVec w := x ||| imm
def andi (x y : BitVec w) : BitVec w := x &&& y

def sllw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (rs2_val.setWidth 5).toNat).signExtend 64

def srlw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (rs2_val.setWidth 5).toNat).signExtend 64

def sraw (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (rs2_val.setWidth 5).toNat).signExtend 64

def sll (x y : BitVec 64) : BitVec 64 := x <<< (y.setWidth 6).toNat
def srl (x y : BitVec 64) : BitVec 64 := x >>> (y.setWidth 6).toNat
def sra (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  rs1_val.sshiftRight (rs2_val.setWidth 6).toNat

def slli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val <<< (shamt.setWidth 6).toNat
def srli64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val >>> (shamt.setWidth 6).toNat
def srai64 (rs1_val shamt : BitVec 64) : BitVec 64 := rs1_val.sshiftRight (shamt.setWidth 6).toNat

def slliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) <<< (shamt.setWidth 5).toNat).signExtend 64

def srliw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32) >>> (shamt.setWidth 5).toNat).signExtend 64

def sraiw (rs1_val shamt : BitVec 64) : BitVec 64 :=
  ((rs1_val.setWidth 32).sshiftRight (shamt.setWidth 5).toNat).signExtend 64

end Riscv

-- ============================================================================
-- Jolt-side value helpers
-- ============================================================================

/-- RV64 `VirtualMovsign` value: all ones if the source sign bit is set,
otherwise zero. -/
def jolt_movsign_value (x : BitVec 64) : BitVec 64 :=
  if x.msb then (-1 : BitVec 64) else 0

/-- RV64 `MULHU` value: high 64 bits of the unsigned 64x64 product. -/
def jolt_mulhu_value (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat / 2^64)

/-- RV64 `SLTU` value: one if `x < y` as unsigned 64-bit integers,
otherwise zero. -/
def jolt_sltu_value (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y))

/-- RV64 `VirtualMULI` value: multiply by the immediate in the 64-bit word
ring.  In the Rust tracer this instruction writes the sign-extended machine
word after a wrapping multiply; for RV64 that is exactly the resulting
64-bit bit pattern. -/
def jolt_virtual_muli_value (x imm : BitVec 64) : BitVec 64 :=
  x * imm

/-- RV64 `VirtualPow2` value: `2 ^ (x[5:0])`, used by `SLL`. -/
def jolt_virtual_pow2_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 6).toNat)

/-- RV64 `VirtualPow2W` value: `2 ^ (x[4:0])`, used by `SLLW`. -/
def jolt_virtual_pow2w_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 5).toNat)

/-- RV64 `VirtualPow2I` value: `2 ^ (imm % 64)`. -/
def jolt_virtual_pow2i_value (imm : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (imm % 64))

/-- RV64 `VirtualPow2IW` value: `2 ^ (imm % 32)`. -/
def jolt_virtual_pow2iw_value (imm : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (imm % 32))

/-- RV64 `VirtualShiftRightBitmask` value.

The tracer first masks the requested shift to six bits, then writes a word
whose trailing-zero count is exactly that shift.  Later `VirtualSRL` and
`VirtualSRA` consume this bitmask by taking `ctz`. -/
def jolt_virtual_shift_right_bitmask_value (x : BitVec 64) : BitVec 64 :=
  let shift := (x.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  BitVec.ofNat 64 (ones <<< shift)

/-- RV64 `VirtualShiftRightBitmaskI` value. -/
def jolt_virtual_shift_right_bitmaski_value (imm : Nat) : BitVec 64 :=
  let shift := imm % 64
  let ones := (1 <<< (64 - shift)) - 1
  BitVec.ofNat 64 (ones <<< shift)

/-- RV64 `VirtualSRLI` value: logical right shift by the trailing-zero count
of the encoded bitmask immediate. -/
def jolt_virtual_srli_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x >>> ctz bitmask

/-- RV64 `VirtualSRAI` value: arithmetic right shift by the trailing-zero
count of the encoded bitmask immediate. -/
def jolt_virtual_srai_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x.sshiftRight (ctz bitmask)

/-- RV64 `VirtualSRL` value: logical right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_srl_value (x bitmask : BitVec 64) : BitVec 64 :=
  x >>> ctz bitmask.toNat

/-- RV64 `VirtualSRA` value: arithmetic right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_sra_value (x bitmask : BitVec 64) : BitVec 64 :=
  x.sshiftRight (ctz bitmask.toNat)

/-- RV64 `VirtualROTRI` value: rotate right by the trailing-zero count of the
encoded bitmask immediate. -/
def jolt_virtual_rotri_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  rotater x (ctz bitmask)

/-- RV64 `VirtualROTRIW` value: rotate the low word right, then zero-extend. -/
def jolt_virtual_rotriw_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  zero_extend (m := 64) (rotater (Sail.BitVec.extractLsb x 31 0) (min (ctz bitmask) 32))

/-- RV64 `VirtualRev8W` value: reverse bytes separately in each 32-bit word. -/
def jolt_virtual_rev8w_value (x : BitVec 64) : BitVec 64 :=
  let lo : BitVec 32 := Sail.BitVec.extractLsb x 31 0
  let hi : BitVec 32 := Sail.BitVec.extractLsb x 63 32
  (rev8 hi) +++ (rev8 lo)

/-- RV64 `VirtualXORROT*` value. -/
def jolt_virtual_xorrot_value (rot : Nat) (x y : BitVec 64) : BitVec 64 :=
  rotater (x ^^^ y) rot

/-- RV64 `VirtualXORROTW*` value: xor low words, rotate, then zero-extend. -/
def jolt_virtual_xorrotw_value (rot : Nat) (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64)
    (rotater ((Sail.BitVec.extractLsb x 31 0) ^^^ (Sail.BitVec.extractLsb y 31 0)) rot)

/-- RV64 `VirtualSignExtendWord` value: sign-extend the low 32 bits to 64
bits. -/
def jolt_virtual_sign_extend_word_value (x : BitVec 64) : BitVec 64 :=
  (x.setWidth 32).signExtend 64

/-- Upper 64 bits of a signed 64×64 multiply. -/
def mulhs (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * b.toInt) / (2 ^ 64))

/-- Signed-division overflow folding rule for `VirtualChangeDivisor`.

When `dividend = INT64_MIN` and `divisor = -1`, signed division would
overflow. Jolt substitutes `1` for the divisor in the verification sequence;
otherwise it passes the divisor through unchanged. -/
def change_divisor_value (dividend divisor : BitVec 64) : BitVec 64 :=
  let mostNeg : BitVec 64 := (1 : BitVec 64) <<< 63
  let negOne : BitVec 64 := -1
  if dividend = mostNeg ∧ divisor = negOne then 1 else divisor

/-- Word-sized version of `change_divisor_value`.

Rust casts both operands to `i32`, so this uses the low 32 bits for the
overflow check and sign-extends the low-word divisor on the normal path. -/
def change_divisor_w_value (dividend divisor : BitVec 64) : BitVec 64 :=
  let dividend := jolt_virtual_sign_extend_word_value dividend
  let divisor := jolt_virtual_sign_extend_word_value divisor
  let i32MinSext : BitVec 64 := -((1 : BitVec 64) <<< 31)
  let negOne : BitVec 64 := -1
  if dividend = i32MinSext ∧ divisor = negOne then 1 else divisor

end
