/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# MULH: RISC-V ≡ Jolt Decomposition

## Instruction (RV64M, Format R)

`MULH rd, rs1, rs2` computes the upper `w` bits of the signed product
of rs1 and rs2, storing the result in rd:
  rd = floor(toInt(rs1) * toInt(rs2) / 2^w)

## Jolt Decomposition

```
VirtualMovsign  v_sx, rs1, 0      -- s_x = sign(rs1)
VirtualMovsign  v_sy, rs2, 0      -- s_y = sign(rs2)
MULHU           v_0,  rs1, rs2    -- v_0 = floor(x' * y' / 2^w)
MUL             v_sx, v_sx, rs2   -- v_sx = s_x * y'
MUL             v_sy, v_sy, rs1   -- v_sy = s_y * x'
ADD             v_0,  v_0,  v_sx  -- v_0 += s_x * y'
ADD             rd,   v_0,  v_sy  -- rd  += s_y * x'
```

## Proof

Using the two's complement identity `toInt(x) = toNat(x) + sign(x) * 2^w`,
we expand the signed product, divide by 2^w, and show the remainder term
`sign(x) * sign(y) * 2^w` vanishes mod 2^w. State-level equality follows
via Format R lifting.
-/

variable {w : Nat}

-- Jolt's decomposition: sign-correct unsigned high multiply via virtual instructions.
def mulhJolt (x y : BitVec w) : BitVec w :=
  let v_sx := Jolt.virtualMovSign x       -- VirtualMovsign v_sx, rs1, 0
  let v_sy := Jolt.virtualMovSign y       -- VirtualMovsign v_sy, rs2, 0
  let v_0  := Jolt.mulhu x y              -- MULHU v_0, rs1, rs2
  let v_sx := Riscv.mul v_sx y             -- MUL v_sx, v_sx, rs2
  let v_sy := Riscv.mul v_sy x            -- MUL v_sy, v_sy, rs1
  let v_0  := Riscv.add v_0 v_sx          -- ADD v_0, v_0, v_sx
  Riscv.add v_0 v_sy                      -- ADD rd,  v_0, v_sy

-- Bridging: VirtualMovSign as ofInt of signExtract (definitional).
private lemma virtualMovSign_eq_ofInt (x : BitVec w) :
    Jolt.virtualMovSign x = BitVec.ofInt w (signExtract x) := rfl

-- Bridging: Riscv.mul of virtualMovSign and y equals ofInt of the Int product.
private lemma virtualMovSign_mul_eq (x y : BitVec w) :
    Riscv.mul (Jolt.virtualMovSign x) y =
      BitVec.ofInt w (signExtract x * (y.toNat : Int)) := by
  unfold Riscv.mul
  rw [virtualMovSign_eq_ofInt]
  have hy : y = BitVec.ofInt w (↑y.toNat : Int) := by
    rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  conv_lhs => rw [hy]
  rw [← BitVec.ofInt_mul]

-- Bridging: MULHU as ofInt of the unsigned high product.
private lemma mulhu_eq_ofInt (x y : BitVec w) :
    (Jolt.mulhu x y : BitVec w) =
      BitVec.ofInt w ((x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)) := by
  unfold Jolt.mulhu
  have h : (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int) =
      ↑(x.toNat * y.toNat / 2 ^ w) := by norm_cast
  rw [h, BitVec.ofInt_natCast]

-- Bridging: the composed mulhJolt equals ofInt of the flat Int expression.
private lemma mulhJolt_eq_ofInt (x y : BitVec w) :
    mulhJolt x y =
      BitVec.ofInt w (
        (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
        + signExtract x * (y.toNat : Int)
        + signExtract y * (x.toNat : Int)) := by
  unfold mulhJolt Riscv.add
  simp only []
  rw [mulhu_eq_ofInt, virtualMovSign_mul_eq x y, virtualMovSign_mul_eq y x]
  rw [← BitVec.ofInt_add, ← BitVec.ofInt_add]

-- Two's complement identity: toInt(x) = toNat(x) + sign(x) * 2^w
private lemma toInt_eq_toNat_add_signExtract_mul (x : BitVec w) :
    (x.toInt : Int) = (x.toNat : Int) + signExtract x * (2 ^ w : Int) := by
  unfold signExtract
  rw [BitVec.toInt_eq_msb_cond]
  split
  · simp; ring
  · simp

-- Product expansion using the two's complement identity on both factors.
private lemma signed_product_expansion (x y : BitVec w) :
    (x.toInt * y.toInt : Int) =
      (x.toNat : Int) * (y.toNat : Int)
      + signExtract x * (y.toNat : Int) * (2 ^ w : Int)
      + signExtract y * (x.toNat : Int) * (2 ^ w : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) * (2 ^ w : Int) := by
  rw [toInt_eq_toNat_add_signExtract_mul x, toInt_eq_toNat_add_signExtract_mul y]
  ring

-- Division pulls out exact multiples of 2^w from the expanded product.
private lemma div_signed_product (x y : BitVec w) :
    x.toInt * y.toInt / (2 ^ w : Int) =
      (x.toNat : Int) * (y.toNat : Int) / (2 ^ w : Int)
      + signExtract x * (y.toNat : Int)
      + signExtract y * (x.toNat : Int)
      + signExtract x * signExtract y * (2 ^ w : Int) := by
  rw [signed_product_expansion]
  have h2w : (2 ^ w : Int) ≠ 0 := by positivity
  have hrearrange :
    (x.toNat : Int) * y.toNat
    + signExtract x * y.toNat * (2 ^ w)
    + signExtract y * x.toNat * (2 ^ w)
    + signExtract x * signExtract y * (2 ^ w) * (2 ^ w)
    = (x.toNat : Int) * y.toNat
    + (signExtract x * y.toNat + signExtract y * x.toNat
       + signExtract x * signExtract y * (2 ^ w)) * (2 ^ w) := by ring
  rw [hrearrange]
  rw [Int.add_mul_ediv_right _ _ h2w]
  ring

-- Pure-function equivalence: Riscv.mulh = mulhJolt
-- The extra sign(x)*sign(y)*2^w term from div_signed_product vanishes mod 2^w.
theorem mulh_eq_mulhJolt (x y : BitVec w) : Riscv.mulh x y = mulhJolt x y := by
  rw [mulhJolt_eq_ofInt]
  unfold Riscv.mulh
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt]
  rw [div_signed_product]
  have key : signExtract x * signExtract y * (2 : Int) ^ w =
    ↑(2 ^ w : Nat) * (signExtract x * signExtract y) := by
    push_cast; ring
  rw [key, Int.add_mul_bmod_self_left]

-- State-level equivalence via Format R lifting (specialized to w=64).
theorem mulh_state_eq (r1 r2 rd : BitVec 5) (s : State) :
    format_r_exec r1 r2 rd (Riscv.mulh (w := 64)) s =
    format_r_exec r1 r2 rd (mulhJolt (w := 64)) s :=
  format_r_ops_eq_of_fns_eq (Riscv.mulh (w := 64)) (mulhJolt (w := 64)) r1 r2 rd s
    (by funext x y; exact mulh_eq_mulhJolt x y)

/-SANITY CHECKS-/
-- Exhaustive check: verify Riscv.mulh == mulhJolt for all 8-bit pairs
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for j in [0:256] do
      let x : BitVec 8 := BitVec.ofNat 8 i
      let y : BitVec 8 := BitVec.ofNat 8 j
      if Riscv.mulh x y != mulhJolt x y then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Exhaustive check passed: Riscv.mulh == mulhJolt for all 65536 8-bit pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"
