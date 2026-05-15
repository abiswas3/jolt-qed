import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULHSU: Rust inline sequence = Sail MULHSU

This file follows the same proof pattern as `Mulh.lean`, but the inline
sequence is longer because Rust computes a signed-by-unsigned high multiply by
first conditionally negating the signed operand and then correcting the high
half of the product.

The statement we want to be the stable API is program-level:

```
projectResult ((JoltISA.execProgram (JoltISA.mulhsuProgram rs2 rs1 rd)).run js)
  =
(execute_MUL rs2 rs1 rd mulhsuOp).run js.sail
```

As in `Mulh.lean`, the proof separates concerns:

1. `JoltISA.mulhsuProgram` is the faithful Rust inline sequence.
2. `mulhsuProgram_eval_jolt_value` proves what this program writes, in Jolt terms.
3. `jolt_mulhsu_value_eq_mulhsu` proves that the Jolt term is Sail's `MULHSU`.

The Rust inline sequence, with allocator choices fixed to `v0` through `v3`, is:

```
VirtualMovsign v0, rs1
ANDI           v1, v0, 1
XOR            v2, rs1, v0
ADD            v2, v2, v1
MULHU          v3, v2, rs2
MUL            v2, v2, rs2
XOR            v3, v3, v0
XOR            v2, v2, v0
ADD            v0, v2, v1
SLTU           v0, v0, v2
ADD            rd, v3, v0
```
-/

def mulhsuOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Unsigned }

/-- Upper 64 bits of a signed-by-unsigned 64x64 multiply. -/
def mulhsu (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * (b.toNat : Int)) / (2 ^ 64))

/-- Auxiliary arithmetic form used internally to relate the Rust sequence to
RV64 `MULHSU`.  It is private because the public proof interface should talk
about either the literal Jolt value `jolt_mulhsu_value` or the Sail value
`mulhsu`. -/
private def jolt_mulhsu_correction_value (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y

/-- The pure value written by the Rust `MULHSU` inline sequence. -/
def jolt_mulhsu_value (x y : BitVec 64) : BitVec 64 :=
  let rs1SignMask := jolt_movsign_value x
  let signBit := rs1SignMask &&& sign_extend (m := 64) (1#12 : BitVec 12)
  let absoluteRs1 := (x ^^^ rs1SignMask) + signBit
  let unsignedHighProduct := jolt_mulhu_value absoluteRs1 y
  let lowProduct := absoluteRs1 * y
  let correctedHighProduct := unsignedHighProduct ^^^ rs1SignMask
  let correctedLowProduct := lowProduct ^^^ rs1SignMask
  correctedHighProduct + jolt_sltu_value (correctedLowProduct + signBit) correctedLowProduct

/-- Extracting the upper half of a 128-bit truncated integer is the same as
division by `2^64`, viewed as a 64-bit bitvector. -/
private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    to_bits_truncate, Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega
/-- The local `mulhsu` value agrees with Sail's generic signed/unsigned
high-half multiply operator. -/
private theorem mulhsu_eq_sail_mulhsu_value (v1 v2 : BitVec 64) :
    mulhsu v1 v2 =
      mult_to_bits_half (l := LeanRV64D.Functions.xlen)
        Signedness.Signed Signedness.Unsigned v1 v2 VectorHalf.High := by
  unfold mulhsu mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.ofInt 64 (v1.toInt * (v2.toNat : Int) / 2^64) =
    BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (v1.toInt * (v2.toNat : Int))) 127 64)
  rw [extract_high64_to_bits_truncate_eq_ofInt_div]
  simp
/-- A 64-bit word below `2^63` has signed interpretation equal to its unsigned
natural-number value. -/
private theorem toInt_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt]
  have hcond : 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
/-- A 64-bit word at least `2^63` has signed interpretation equal to its
unsigned value minus `2^64`. -/
private theorem toInt_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) - (18446744073709551616 : Int) := by
  rw [BitVec.toInt]
  have hcond : ¬ 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
  norm_num
/-- Xoring a 64-bit word with all ones complements its natural-number value
inside the `2^64` range. -/
private theorem xor_neg_one_toNat (x : BitVec 64) :
    (x ^^^ (-1 : BitVec 64)).toNat =
      18446744073709551616 - 1 - x.toNat := by
  rw [show x ^^^ (-1 : BitVec 64) = ~~~x by bv_decide]
  rw [BitVec.toNat_not]
/-- For a negative signed 64-bit word, `xor -1` followed by `+ 1` computes the
magnitude `2^64 - x.toNat`. -/
private theorem abs_neg_toNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1).toNat =
      18446744073709551616 - x.toNat := by
  rw [BitVec.toNat_add, xor_neg_one_toNat]
  have hxpos : 0 < x.toNat := by omega
  rw [show (1 : BitVec 64).toNat = 1 by decide]
  norm_num
  omega
/-- The bitvector absolute-value expression for a negative operand is equal to
the corresponding `BitVec.ofNat` magnitude. -/
private theorem abs_neg_eq_ofNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1) =
      BitVec.ofNat 64 (18446744073709551616 - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [abs_neg_toNat x hx, BitVec.toNat_ofNat]
  have hxpos : 0 < x.toNat := by omega
  norm_num
  omega

/-- Arithmetic correction for the negative signed operand case in `MULHSU`. -/
private theorem mulhsu_corr_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 =
      ((((a : Int) - 18446744073709551616) * (b : Int) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) * (b : Int) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) by
    rw [Nat.cast_mul]
    ring]
  omega

/-- If the complementary product has zero low half, the high-half quotient of
the original product is exactly the unsigned operand minus the complementary
quotient. -/
private theorem div_complement_mod_zero (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  omega

/-- If the complementary product has nonzero low half, the high-half quotient
of the original product is one less than the zero-remainder case. -/
private theorem div_complement_mod_pos (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : ¬ (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) - 1 := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  have hrpos : 0 < (18446744073709551616 - a) * b %
      18446744073709551616 := by omega
  have hrlt : (18446744073709551616 - a) * b %
      18446744073709551616 < 18446744073709551616 :=
    Nat.mod_lt _ (by norm_num)
  omega

/-- Modular identity for the negated high half when the low-half correction
does not borrow. -/
private theorem neg_high_mod_zero (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q ≤ b) :
    (18446744073709551616 - q) % 18446744073709551616 =
      (b - q + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.sub_zero]
    rw [show b + 18446744073709551615 * b =
        18446744073709551616 * b by omega]
    rw [Nat.mul_mod_right]
  · have hqpos : 0 < q := by omega
    have hbpos : 0 < b := by omega
    have hqN : q < 18446744073709551616 := by omega
    have hleft : (18446744073709551616 - q) %
        18446744073709551616 = 18446744073709551616 - q := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hleft]
    have hright_eq :
        b - q + 18446744073709551615 * b =
          18446744073709551616 * (b - 1) +
            (18446744073709551616 - q) := by
      omega
    rw [hright_eq]
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp
    exact hleft.symm

/-- Modular identity for the negated high half when the low-half correction
does borrow. -/
private theorem neg_high_mod_pos (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q + 1 ≤ b) :
    (18446744073709551616 - 1 - q) % 18446744073709551616 =
      (b - q - 1 + 18446744073709551615 * b) %
        18446744073709551616 := by
  have hbpos : 0 < b := by omega
  have hqN : q < 18446744073709551616 := by omega
  have hleft : (18446744073709551616 - 1 - q) %
      18446744073709551616 = 18446744073709551616 - 1 - q := by
    apply Nat.mod_eq_of_lt
    omega
  rw [hleft]
  have hright_eq :
      b - q - 1 + 18446744073709551615 * b =
        18446744073709551616 * (b - 1) +
          (18446744073709551616 - 1 - q) := by
    omega
  rw [hright_eq]
  rw [Nat.add_mod, Nat.mul_mod_right]
  simp
  exact hleft.symm

/-- The high-half correction produced by the Rust/Jolt sequence agrees with
the compact signed/unsigned correction formula. -/
private theorem neg_high_eq_mulhsu_correction (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hbN : b < 18446744073709551616) :
    (18446744073709551615 -
          ((18446744073709551616 - a) * b /
            18446744073709551616) +
        (if ((18446744073709551615 -
                ((18446744073709551616 - a) * b %
                  18446744073709551616) + 1) %
              18446744073709551616) <
            18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616)
          then 1 else 0)) % 18446744073709551616 =
      (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hr : (18446744073709551616 - a) * b %
      18446744073709551616 = 0
  · rw [div_complement_mod_zero a b ha haN hr]
    simp [hr]
    have hq_le : (18446744073709551616 - a) * b /
        18446744073709551616 ≤ b := by
      apply Nat.div_le_of_le_mul
      have hm : 18446744073709551616 - a ≤ 18446744073709551616 :=
        Nat.sub_le _ _
      nlinarith
    rw [show 18446744073709551615 -
        ((18446744073709551616 - a) * b / 18446744073709551616) + 1 =
          18446744073709551616 -
            ((18446744073709551616 - a) * b /
              18446744073709551616) by omega]
    exact neg_high_mod_zero b
      ((18446744073709551616 - a) * b / 18446744073709551616)
      hbN hq_le
  · have hcond : ¬
        ((18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616) + 1) %
            18446744073709551616) <
          18446744073709551615 -
            ((18446744073709551616 - a) * b %
              18446744073709551616) := by
      have hrpos : 0 < (18446744073709551616 - a) * b %
          18446744073709551616 := by omega
      have hrlt : (18446744073709551616 - a) * b %
          18446744073709551616 < 18446744073709551616 :=
        Nat.mod_lt _ (by norm_num)
      rw [show 18446744073709551615 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) + 1 =
        18446744073709551616 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) by omega]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [div_complement_mod_pos a b ha haN hr]
    simp [hcond]
    apply neg_high_mod_pos
    · exact hbN
    · have hbpos : 0 < b := by
        by_contra hb
        have hb0 : b = 0 := by omega
        simp [hb0] at hr
      have hm_lt : 18446744073709551616 - a <
          18446744073709551616 := by omega
      have hdivlt : (18446744073709551616 - a) * b /
          18446744073709551616 < b := by
        rw [Nat.div_lt_iff_lt_mul
          (by norm_num : 0 < 18446744073709551616)]
        nlinarith
      omega

/-- The literal Rust/Jolt `MULHSU` value simplifies to the compact correction
formula `jolt_mulhu_value x y + sign(x) * y`. -/
private theorem jolt_mulhsu_value_eq_correction (x y : BitVec 64) :
    jolt_mulhsu_value x y = jolt_mulhsu_correction_value x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value
    rw [jolt_sltu_value_eq_zero_of_not_lt]
    · apply BitVec.eq_of_toNat_eq
      simp
    · simp
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    change (jolt_mulhu_value
          ((x ^^^ (-1 : BitVec 64)) +
            ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12))) y ^^^ (-1 : BitVec 64)) +
        jolt_sltu_value (((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) + 1)
          ((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) =
      jolt_mulhu_value x y + (-1 : BitVec 64) * y
    rw [show ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12)) =
      1 by decide]
    rw [abs_neg_eq_ofNat x hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      (jolt_mulhu_value (BitVec.ofNat 64 (18446744073709551616 - x.toNat)) y)]
    rw [jolt_sltu_value_toNat]
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      ((BitVec.ofNat 64 (18446744073709551616 - x.toNat)) * y)]
    unfold jolt_mulhu_value
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofNat, BitVec.toNat_mul]
    rw [show (1 : BitVec 64).toNat = 1 by decide]
    rw [show (-1 : BitVec 64).toNat = 18446744073709551615 by decide]
    norm_num
    have hNx : (18446744073709551616 - x.toNat) %
        18446744073709551616 = 18446744073709551616 - x.toNat := by
      apply Nat.mod_eq_of_lt
      have hxpos : 0 < x.toNat := by omega
      omega
    rw [hNx]
    have hq1 : (18446744073709551616 - x.toNat) * y.toNat /
        18446744073709551616 < 18446744073709551616 := by
      rw [Nat.div_lt_iff_lt_mul
        (by norm_num : 0 < 18446744073709551616)]
      have hxpos : 0 < x.toNat := by omega
      have hm_lt : 18446744073709551616 - x.toNat <
          18446744073709551616 := by omega
      nlinarith [hm_lt, y.isLt]
    rw [Nat.mod_eq_of_lt hq1]
    exact neg_high_eq_mulhsu_correction x.toNat y.toNat hx x.isLt y.isLt

/-- The compact signed/unsigned correction formula equals the RV64 `MULHSU`
value. -/
private theorem jolt_mulhsu_correction_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_correction_value x y = mulhsu x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_toNat_lt_half x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_half_le x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    exact mulhsu_corr_neg_arith x.toNat y.toNat

/-- The literal Rust/Jolt `MULHSU` value equals the Sail/RISC-V `MULHSU` value. -/
private theorem jolt_mulhsu_value_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_value x y = mulhsu x y := by
  rw [jolt_mulhsu_value_eq_correction, jolt_mulhsu_correction_eq_mulhsu]

/-- Factor Sail's generated `execute_MUL` body for `MULHSU` into the simple
shape used by the generic R-type equivalence bridge. -/
theorem execute_MULHSU_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhsuOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhsu v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhsuOp, mulhsu_eq_sail_mulhsu_value, bind_pure_comp]

/-- Evaluate the Jolt `MULHSU` expansion to the pure value it writes.

This theorem is intentionally about `jolt_mulhsu_value`, not `mulhsu`.  It is
the monadic/transcription theorem: assuming the two architectural source reads
succeed, executing the instruction list produced from Rust writes the exact
Jolt expression encoded by that list.

The checkpoint states mirror the eleven instructions:

* `js_afterRs1SignMask`:  `v0 = sign(rs1)`
* `js_afterSignBit`:  `v1 = sign(rs1) & 1`
* `js_afterAbsXor`:  `v2 = rs1 xor sign(rs1)`
* `js_afterAbsoluteRs1`:  `v2 = (rs1 xor sign(rs1)) + (sign(rs1) & 1)`
* `js_afterMulhu`:  `v3 = unsigned_high(v2 * rs2)`
* `js_afterMulLow`:  `v2 = low(v2 * rs2)`
* `js_afterHighCorrectionXor`:  `v3 = v3 xor sign(rs1)`
* `js_afterLowCorrectionXor`:  `v2 = v2 xor sign(rs1)`
* `js_afterCarryCandidate`:  `v0 = v2 + (sign(rs1) & 1)`
* `js_afterCarry`: `v0 = if v0 < v2 then 1 else 0`
* `js_afterFinalAdd`: `rd = v3 + v0`

The proof is long because every intermediate virtual-register write is exposed.
That is deliberate for this first version: the goal is to make the hand
transcription easy to audit before we automate this pattern. -/
theorem mulhsuProgram_eval_jolt_value (rs2 rs1 rd : regidx)
    (js : SailJoltState) (v1 v2 : BitVec 64)
    (h1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.mulhsuProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (jolt_mulhsu_value v1 v2) := by
  -- Local names for the values that appear in Rust's inline sequence.  They are
  -- arranged in program order, so the evaluation proof below can be
  -- read as a value trace.
  let rs1SignMask := jolt_movsign_value v1
  let signBit := rs1SignMask &&& sign_extend (m := 64) (1#12 : BitVec 12)
  let absoluteValueXor := v1 ^^^ rs1SignMask
  let absoluteRs1 := absoluteValueXor + signBit
  let unsignedHighProduct := jolt_mulhu_value absoluteRs1 v2
  let lowProduct := absoluteRs1 * v2
  let correctedHighProduct := unsignedHighProduct ^^^ rs1SignMask
  let correctedLowProduct := lowProduct ^^^ rs1SignMask
  let carryCandidate := correctedLowProduct + signBit
  let carryCorrection := jolt_sltu_value carryCandidate correctedLowProduct
  let mulhsuJoltResult := jolt_mulhsu_value v1 v2

  -- After `VirtualMovsign v0, rs1`.
  let js_afterRs1SignMask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then rs1SignMask else js.vregs r }
  -- After `ANDI v1, v0, 1`.
  let js_afterSignBit : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then signBit else js_afterRs1SignMask.vregs r }
  -- After `XOR v2, rs1, v0`.
  let js_afterAbsXor : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then absoluteValueXor else js_afterSignBit.vregs r }
  -- After `ADD v2, v2, v1`.
  let js_afterAbsoluteRs1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then absoluteRs1 else js_afterAbsXor.vregs r }
  -- After `MULHU v3, v2, rs2`.
  let js_afterMulhu : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (3 : JoltISA.VReg) then unsignedHighProduct else js_afterAbsoluteRs1.vregs r }
  -- After `MUL v2, v2, rs2`.
  let js_afterMulLow : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then lowProduct else js_afterMulhu.vregs r }
  -- After `XOR v3, v3, v0`.
  let js_afterHighCorrectionXor : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (3 : JoltISA.VReg) then correctedHighProduct else js_afterMulLow.vregs r }
  -- After `XOR v2, v2, v0`.
  let js_afterLowCorrectionXor : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then correctedLowProduct else js_afterHighCorrectionXor.vregs r }
  -- After `ADD v0, v2, v1`.
  let js_afterCarryCandidate : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then carryCandidate else js_afterLowCorrectionXor.vregs r }
  -- After `SLTU v0, v0, v2`.
  let js_afterCarry : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then carryCorrection else js_afterCarryCandidate.vregs r }
  -- The final `ADD` writes to the architectural register file, so we use
  -- `wX_shape` to name the Sail state produced by that write.
  obtain ⟨s_afterFinalAdd, h_final_add_write⟩ := wX_shape rd mulhsuJoltResult js.sail
  -- After `ADD rd, v3, v0`.
  let js_afterFinalAdd : SailJoltState := { sail := s_afterFinalAdd, vregs := js_afterCarry.vregs }

  -- All states before the final write keep `sail` unchanged, so original
  -- architectural read facts can be reused at the later checkpoints.
  have h_rs1_reads_v1_after_sign_bit : rX_bits rs1 js_afterSignBit.sail = .ok v1 js_afterSignBit.sail := by
    simpa (config := { decide := true }) only [js_afterSignBit, js_afterRs1SignMask] using h1
  have h_rs2_reads_v2_after_absolute_value : rX_bits rs2 js_afterAbsoluteRs1.sail = .ok v2 js_afterAbsoluteRs1.sail := by
    simpa (config := { decide := true }) only [js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask] using h2
  have h_rs2_reads_v2_after_mulhu : rX_bits rs2 js_afterMulhu.sail = .ok v2 js_afterMulhu.sail := by
    simpa (config := { decide := true }) only [js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask] using h2
  have h_rs1_sign_mask_succeeds :
      JoltISA.execInstr (.VirtualMovsign (.vreg (0 : JoltISA.VReg)) (.xreg rs1)) js =
        .ok RETIRE_SUCCESS js_afterRs1SignMask := by
    simpa (config := { decide := true }) only [js_afterRs1SignMask, rs1SignMask] using
      (JoltISA.movsign_run_vreg_xreg (vd := (0 : JoltISA.VReg)) (rs := rs1) js v1 h1)
  have h_sign_bit_succeeds :
      JoltISA.execInstr (.ANDI (.vreg (1 : JoltISA.VReg)) (.vreg (0 : JoltISA.VReg))
        (1 : BitVec 12)) js_afterRs1SignMask = .ok RETIRE_SUCCESS js_afterSignBit := by
    simpa (config := { decide := true }) only [js_afterSignBit, js_afterRs1SignMask, signBit, rs1SignMask] using
      (JoltISA.andi_run_vreg_vreg (vd := (1 : JoltISA.VReg))
        (vs := (0 : JoltISA.VReg)) (imm := (1 : BitVec 12)) js_afterRs1SignMask)
  have h_absolute_value_xor_succeeds :
      JoltISA.execInstr (.XOR (.vreg (2 : JoltISA.VReg)) (.xreg rs1)
        (.vreg (0 : JoltISA.VReg))) js_afterSignBit = .ok RETIRE_SUCCESS js_afterAbsXor := by
    simpa (config := { decide := true }) only [js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, absoluteValueXor, rs1SignMask] using
      (JoltISA.xor_run_vreg_xreg_vreg (vd := (2 : JoltISA.VReg))
        (lhs := rs1) (rhs := (0 : JoltISA.VReg)) js_afterSignBit v1 h_rs1_reads_v1_after_sign_bit)
  have h_absolute_value_add_succeeds :
      JoltISA.execInstr (.ADD (.vreg (2 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.vreg (1 : JoltISA.VReg))) js_afterAbsXor = .ok RETIRE_SUCCESS js_afterAbsoluteRs1 := by
    simpa (config := { decide := true }) only [js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, absoluteRs1, absoluteValueXor, signBit] using
      (JoltISA.add_run_vreg_vreg_vreg (vd := (2 : JoltISA.VReg))
        (lhs := (2 : JoltISA.VReg)) (rhs := (1 : JoltISA.VReg)) js_afterAbsXor)
  have h_mulhu_succeeds :
      JoltISA.execInstr (.MULHU (.vreg (3 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.xreg rs2)) js_afterAbsoluteRs1 = .ok RETIRE_SUCCESS js_afterMulhu := by
    simpa (config := { decide := true }) only [js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, unsignedHighProduct, absoluteRs1] using
      (JoltISA.mulhu_run_vreg_vreg_xreg (vd := (3 : JoltISA.VReg))
        (lhs := (2 : JoltISA.VReg)) (rhs := rs2) js_afterAbsoluteRs1 v2 h_rs2_reads_v2_after_absolute_value)
  have h_low_mul_succeeds :
      JoltISA.execInstr (.MUL (.vreg (2 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.xreg rs2)) js_afterMulhu = .ok RETIRE_SUCCESS js_afterMulLow := by
    simpa (config := { decide := true }) only [js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, lowProduct, absoluteRs1] using
      (JoltISA.mul_run_vreg_vreg_xreg (vd := (2 : JoltISA.VReg))
        (lhs := (2 : JoltISA.VReg)) (rhs := rs2) js_afterMulhu v2 h_rs2_reads_v2_after_mulhu)
  have h_high_correction_xor_succeeds :
      JoltISA.execInstr (.XOR (.vreg (3 : JoltISA.VReg)) (.vreg (3 : JoltISA.VReg))
        (.vreg (0 : JoltISA.VReg))) js_afterMulLow = .ok RETIRE_SUCCESS js_afterHighCorrectionXor := by
    simpa (config := { decide := true }) only [js_afterHighCorrectionXor, js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, correctedHighProduct, unsignedHighProduct, rs1SignMask] using
      (JoltISA.xor_run_vreg_vreg_vreg (vd := (3 : JoltISA.VReg))
        (lhs := (3 : JoltISA.VReg)) (rhs := (0 : JoltISA.VReg)) js_afterMulLow)
  have h_low_correction_xor_succeeds :
      JoltISA.execInstr (.XOR (.vreg (2 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.vreg (0 : JoltISA.VReg))) js_afterHighCorrectionXor = .ok RETIRE_SUCCESS js_afterLowCorrectionXor := by
    simpa (config := { decide := true }) only [js_afterLowCorrectionXor, js_afterHighCorrectionXor, js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, correctedLowProduct, lowProduct, rs1SignMask] using
      (JoltISA.xor_run_vreg_vreg_vreg (vd := (2 : JoltISA.VReg))
        (lhs := (2 : JoltISA.VReg)) (rhs := (0 : JoltISA.VReg)) js_afterHighCorrectionXor)
  have h_carry_candidate_add_succeeds :
      JoltISA.execInstr (.ADD (.vreg (0 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.vreg (1 : JoltISA.VReg))) js_afterLowCorrectionXor = .ok RETIRE_SUCCESS js_afterCarryCandidate := by
    simpa (config := { decide := true }) only [js_afterCarryCandidate, js_afterLowCorrectionXor, js_afterHighCorrectionXor, js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, carryCandidate, correctedLowProduct, signBit] using
      (JoltISA.add_run_vreg_vreg_vreg (vd := (0 : JoltISA.VReg))
        (lhs := (2 : JoltISA.VReg)) (rhs := (1 : JoltISA.VReg)) js_afterLowCorrectionXor)
  have h_sltu_succeeds :
      JoltISA.execInstr (.SLTU (.vreg (0 : JoltISA.VReg)) (.vreg (0 : JoltISA.VReg))
        (.vreg (2 : JoltISA.VReg))) js_afterCarryCandidate = .ok RETIRE_SUCCESS js_afterCarry := by
    simpa (config := { decide := true }) only [js_afterCarry, js_afterCarryCandidate, js_afterLowCorrectionXor, js_afterHighCorrectionXor, js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, carryCorrection, carryCandidate, correctedLowProduct] using
      (JoltISA.sltu_run_vreg_vreg_vreg (vd := (0 : JoltISA.VReg))
        (lhs := (0 : JoltISA.VReg)) (rhs := (2 : JoltISA.VReg)) js_afterCarryCandidate)
  have h_final_add_write_input : wX_bits rd
      (js_afterCarry.vregs (3 : JoltISA.VReg) + js_afterCarry.vregs (0 : JoltISA.VReg)) js_afterCarry.sail =
        .ok () s_afterFinalAdd := by
    simpa (config := { decide := true }) only [js_afterCarry, js_afterCarryCandidate, js_afterLowCorrectionXor, js_afterHighCorrectionXor, js_afterMulLow, js_afterMulhu, js_afterAbsoluteRs1, js_afterAbsXor, js_afterSignBit, js_afterRs1SignMask, mulhsuJoltResult, carryCorrection,
      carryCandidate, correctedLowProduct, correctedHighProduct, lowProduct, unsignedHighProduct, absoluteRs1, absoluteValueXor, signBit, rs1SignMask] using h_final_add_write
  have h_final_add_succeeds :
      JoltISA.execInstr (.ADD (.xreg rd) (.vreg (3 : JoltISA.VReg))
        (.vreg (0 : JoltISA.VReg))) js_afterCarry = .ok RETIRE_SUCCESS js_afterFinalAdd := by
    simpa (config := { decide := true }) only [js_afterFinalAdd] using
      (JoltISA.add_run_xreg_vreg_vreg (rd := rd) (lhs := (3 : JoltISA.VReg))
        (rhs := (0 : JoltISA.VReg)) js_afterCarry s_afterFinalAdd h_final_add_write_input)
  refine ⟨js_afterFinalAdd, ?_, ?_⟩
  · simp only [JoltISA.mulhsuProgram, JoltISA.execProgram_instr, EStateM.run,
      bind, EStateM.bind]
    rw [h_rs1_sign_mask_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_sign_bit_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_absolute_value_xor_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_absolute_value_add_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_mulhu_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_low_mul_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_high_correction_xor_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_low_correction_xor_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_carry_candidate_add_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_sltu_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_final_add_succeeds]
    simp [JoltISA.execProgram, RETIRE_SUCCESS, pure, EStateM.pure, js_afterFinalAdd]
  -- Identify the Sail write produced by the final instruction with a write of
  -- the pure Jolt value computed by the full sequence.
  change s_afterFinalAdd = stateAfterWrite js.sail rd (jolt_mulhsu_value v1 v2)
  rw [wX_bits_eq_stateAfterWrite rd mulhsuJoltResult js.sail s_afterFinalAdd h_final_add_write]

/-- Combine Jolt-value evaluation with the arithmetic theorem for `MULHSU`.

The evaluation theorem knows that the program writes `jolt_mulhsu_value`; this
wrapper packages the well-formed source reads and rewrites the final state to
the Sail value `mulhsu`. -/
theorem mulhsuProgram_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (jsf : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.mulhsuProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhsu v1 v2) := by
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  obtain ⟨jsf, hrun, hsail⟩ := mulhsuProgram_eval_jolt_value rs2 rs1 rd js v1 v2 h1 h2
  refine ⟨jsf, v1, v2, h1, h2, hrun, ?_⟩
  simpa only [jolt_mulhsu_value_eq_mulhsu] using hsail

/-- Main program-level theorem: interpreting the Jolt ISA `MULHSU` expansion
has the same projected architectural result as Sail's `MULHSU` semantics. -/
theorem mulhsuProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.mulhsuProgram rs2 rs1 rd)).run js) =
    (execute_MUL rs2 rs1 rd mulhsuOp).run js.sail :=
  rtype_eq_sail_uniform
    (f := mulhsu)
    (execute_MULHSU_factored rs2 rs1 rd)
    (mulhsuProgram_concrete rs2 rs1 rd hrd js hwf)

end
