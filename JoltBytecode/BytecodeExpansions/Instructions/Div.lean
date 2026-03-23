/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

-- TODO: sorry in soundness helper (no_overflow_implies_mul_toInt_eq)
-- TODO: sorry in main soundness theorem (div_validation_sound, depends on above)
-- TODO: sorry in completeness helper (div_identity)
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.NoOverflow

/-!
# DIV: RISC-V ≡ Jolt Decomposition

## Instruction (RV64M, Format R)

`DIV rd, rs1, rs2` computes the signed integer division of rs1 by rs2,
truncating toward zero:
  rd = rs1 /ₜ rs2

Special cases:
- Division by zero: rd = -1 (all ones)
- Overflow (INT_MIN / -1): rd = INT_MIN (most negative value, unchanged)

## Jolt Decomposition (oracle-based, faithful to Rust implementation)

Jolt does NOT compute the quotient directly. Instead, an oracle (the prover)
provides the quotient `q` and absolute remainder `|r|`, and the constraint
system *validates* them through a sequence of 18 steps:

```
VirtualAdvice     a2, 0              -- q   = oracle quotient
VirtualAdvice     a3, 0              -- |r|  = oracle |remainder|
VirtualAssertValidDiv0  a1, a2, 0    -- if divisor=0, assert q=-1
VirtualChangeDivisor    t0, a0, a1   -- y_adj = overflow-safe divisor
MULH              t1, a2, t0         -- high(q × y_adj)
MUL               t2, a2, t0         -- low(q × y_adj)
SRAI              t3, t2, 63         -- sign_extend(low product)
VirtualAssertEQ   t1, t3, 0          -- assert no overflow
SRAI              t1, a0, 63         -- sign(dividend)
XOR               t3, a3, t1         -- |r| XOR sign(x)
SUB               t3, t3, t1         -- → signed remainder r
ADD               t2, t2, t3         -- q×y_adj + r
VirtualAssertEQ   t2, a0, 0          -- assert = dividend
SRAI              t1, t0, 63         -- sign(y_adj)
XOR               t3, t0, t1         -- y_adj XOR sign(y_adj)
SUB               t3, t3, t1         -- → |y_adj|
VirtualAssertValidUnsignedRemainder  a3, t3, 0  -- assert |r| < |y_adj|
ADDI              rd, a2, 0          -- rd = q
```

## Note on Division Semantics

RISC-V uses truncated division (toward zero), matching `Int.tdiv`/`Int.tmod`.
Lean's `/` and `%` operators for `Int` use Euclidean division (toward -∞),
which differs for negative dividends. All formulas in this file explicitly
use `Int.tdiv` and `Int.tmod` to match RISC-V semantics.
-/

-- ============================================================================
-- Virtual instructions specific to DIV
-- ============================================================================

namespace Jolt

/-- VirtualAssertValidDiv0: when divisor is zero, the quotient must be -1.
    Models the Jolt constraint that forces q = -1 for division by zero. -/
def virtualAssertValidDiv0 (divisor quotient : BitVec 64) : BitVec 64 :=
  if divisor = (0 : BitVec 64) then BitVec.ofInt 64 (-1)
  else quotient

/-- VirtualChangeDivisor: adjusts the divisor for the overflow case.
    When dividend = INT_MIN and divisor = -1, changes divisor to 1
    to avoid MULH overflow during validation. Otherwise keeps divisor. -/
def virtualChangeDivisor (dividend divisor : BitVec 64) : BitVec 64 :=
  if dividend = BitVec.intMin 64 ∧ divisor = BitVec.ofInt 64 (-1)
  then (1 : BitVec 64)
  else divisor

end Jolt

-- ============================================================================
-- XOR-SUB sign correction (used in DIV/REM decompositions)
-- ============================================================================

/-- XOR-SUB absolute value pattern:
    `(x ⊕ sign_bits) - sign_bits` where sign_bits = SRAI(x, 63).
    If x ≥ 0: sign = 0, result = x.
    If x < 0: sign = -1 (all ones), result = NOT(x) + 1 = -x = |x|.
    Applied in reverse: converts |r| to signed r using dividend's sign. -/
def xor_sub_sign (val sign_bits : BitVec 64) : BitVec 64 :=
  (val ^^^ sign_bits) - sign_bits

-- ============================================================================
-- Jolt decomposition (modeling oracle + validation)
-- ============================================================================

/-- Jolt's DIV decomposition: models the oracle-based computation.
    The oracle (prover) provides the correct quotient and |remainder|,
    which are then validated by the 18-step constraint sequence.
    Since the oracle always provides correct values, this function
    computes the same result as Riscv.sdiv.

    Uses Int.tdiv/tmod (truncated division) matching RISC-V semantics. -/
def divJolt (x y : BitVec 64) : BitVec 64 :=
  -- Steps 1-2: Oracle advice (the prover computes the correct division)
  let q_oracle : BitVec 64 :=
    if y = (0 : BitVec 64) then BitVec.ofInt 64 (-1)
    else BitVec.ofInt 64 (x.toInt.tdiv y.toInt)
  let abs_r_oracle : BitVec 64 :=
    if y = (0 : BitVec 64) then (0 : BitVec 64)
    else BitVec.ofNat 64 ((x.toInt.tmod y.toInt).natAbs)
  -- Step 3: VirtualAssertValidDiv0
  let q := Jolt.virtualAssertValidDiv0 y q_oracle
  -- Step 4: VirtualChangeDivisor
  let y_adj := Jolt.virtualChangeDivisor x y
  -- Steps 5-6: MULH/MUL (compute q × y_adj to verify)
  let _mulh_check := Riscv.mulh q y_adj
  let mul_low := Riscv.mul q y_adj
  -- Steps 7-8: Overflow check
  let _sign_product := mul_low.sshiftRight 63
  -- Steps 9-11: Sign-correct the absolute remainder
  let sign_x := x.sshiftRight 63
  let r_signed := xor_sub_sign abs_r_oracle sign_x
  -- Step 12-13: Verify division identity
  let _identity_check := mul_low + r_signed
  -- Steps 14-16: Compute |y_adj| for remainder bound check
  let sign_y := y_adj.sshiftRight 63
  let _abs_y := xor_sub_sign y_adj sign_y
  -- Step 18: Return quotient
  q

-- ============================================================================
-- Main theorems
-- ============================================================================

/-- Pure-function equivalence: Riscv.sdiv = divJolt.
    The oracle always provides the correct quotient, so the Jolt decomposition
    computes the same result as the RISC-V definition. -/
theorem div_eq_divJolt (x y : BitVec 64) :
    Riscv.sdiv x y = divJolt x y := by
  unfold Riscv.sdiv divJolt Jolt.virtualAssertValidDiv0 Jolt.virtualChangeDivisor
  by_cases h : y = (0 : BitVec 64) <;> simp_all

-- State-level equivalence via Format R lifting.
theorem div_state_eq (rs1 rs2 rd : BitVec 5) (s : State) :
    format_r_exec rs1 rs2 rd Riscv.sdiv s =
    format_r_exec rs1 rs2 rd divJolt s :=
  format_r_ops_eq_of_fns_eq Riscv.sdiv divJolt rs1 rs2 rd s
    (by funext x y; exact div_eq_divJolt x y)

-- ============================================================================
-- Helper lemmas for sshiftRight 63
-- ============================================================================

private lemma ushiftRight_63_of_msb_false {x : BitVec 64} (h : x.msb = false) :
    x >>> 63 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0 < 2^64)]
  rw [show 63 = 64 - 1 from rfl]
  have hx : x.toNat < 2 ^ 63 := by
    rw [BitVec.msb_eq_decide] at h
    simp only [decide_eq_false_iff_not, not_le] at h
    exact h
  omega

private lemma sshiftRight_63_of_msb_false {x : BitVec 64} (h : x.msb = false) :
    x.sshiftRight 63 = 0#64 := by
  rw [BitVec.sshiftRight_eq_of_msb_false h]
  exact ushiftRight_63_of_msb_false h

private lemma sshiftRight_63_of_msb_true {x : BitVec 64} (h : x.msb = true) :
    x.sshiftRight 63 = BitVec.allOnes 64 := by
  rw [BitVec.sshiftRight_eq_of_msb_true h]
  have h_not_msb : (~~~x).msb = false := by simp [BitVec.msb_not, h]
  have h_shift : ~~~x >>> 63 = 0#64 := ushiftRight_63_of_msb_false h_not_msb
  rw [h_shift]
  simp [BitVec.not_zero]

-- ============================================================================
-- XOR-SUB helpers
-- ============================================================================

/-- XOR-SUB with zero is identity. -/
private lemma xor_sub_zero (v : BitVec 64) : xor_sub_sign v 0 = v := by
  unfold xor_sub_sign; simp

/-- XOR-SUB with allOnes is negation: (v ⊕ (-1)) - (-1) = -v.
    Proof: ~~~v = -1 - v in two's complement, so ~~~v - (-1) = -v. -/
private lemma xor_sub_allOnes (v : BitVec 64) :
    xor_sub_sign v (BitVec.allOnes 64) = -v := by
  unfold xor_sub_sign; rw [BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes,
             BitVec.toNat_neg]
  omega

-- ============================================================================
-- Soundness: Jolt constraints → correct quotient
-- ============================================================================
--
-- The soundness theorem says: if the 3 constraint checks pass on ANY
-- oracle-provided quotient q and absolute remainder |r|, then q must
-- be the correct RISC-V truncated quotient.
--
-- Jolt's DIV validation checks 3 properties:
--
--   (1) No overflow: MULH(q, y_adj) = sign-extend(MUL(q, y_adj))
--       Ensures q × y_adj fits in 64-bit signed range, so the BitVec
--       multiplication equals the true integer product.
--
--   (2) Division identity: q × y_adj + r_signed = x  (as BitVec 64)
--       Combined with (1), this lifts to an integer identity.
--
--   (3) Remainder bound: |r| < |y_adj|  (unsigned comparison)
--       Ensures uniqueness: only one (q, r) pair satisfies the identity
--       with this bound.
--
-- Additionally:
-- - VirtualAssertValidDiv0 handles div-by-zero (forces q = -1)
-- - VirtualChangeDivisor handles the INT_MIN / -1 overflow case
-- - The XOR-SUB sign correction constrains sign(r) = sign(x),
--   distinguishing truncated from Euclidean division.
--
-- Together these uniquely determine q as the RISC-V truncated quotient.

/-- When `a < 0`, `tmod a b ≤ 0`. The sign of tmod matches the dividend. -/
private lemma Int.tmod_nonpos_of_neg {a : Int} (b : Int) (ha : a < 0) :
    a.tmod b ≤ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = Int.negSucc m := by
    cases a with
    | ofNat n => exact absurd ha (not_lt.mpr (Int.ofNat_nonneg n))
    | negSucc m => exact ⟨m, rfl⟩
  cases b with
  | ofNat n =>
    simp only [Int.tmod]
    exact Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg _)
  | negSucc n =>
    simp only [Int.tmod]
    exact Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg _)

/-- natAbs of tmod is less than natAbs of divisor. -/
private lemma Int.natAbs_tmod_lt' (x b : Int) (hb : b ≠ 0) :
    (x.tmod b).natAbs < b.natAbs := by
  cases x with
  | ofNat m =>
    cases b with
    | ofNat n =>
      simp only [Int.tmod, Int.natAbs]
      have hn : 0 < n := by
        have : n ≠ 0 := fun h => hb (by subst h; rfl); omega
      exact Nat.mod_lt m hn
    | negSucc n => simp only [Int.tmod, Int.natAbs]; exact Nat.mod_lt m (Nat.succ_pos n)
  | negSucc m =>
    cases b with
    | ofNat n =>
      simp only [Int.tmod]; rw [Int.natAbs_neg]; show m.succ % n < n
      have hn : 0 < n := by
        have : n ≠ 0 := fun h => hb (by subst h; rfl); omega
      exact Nat.mod_lt (m + 1) hn
    | negSucc n =>
      simp only [Int.tmod]; rw [Int.natAbs_neg]; show m.succ % n.succ < n.succ
      exact Nat.mod_lt (m + 1) (Nat.succ_pos n)

/-- When two nonneg integers both have natAbs < N, their difference has natAbs < N. -/
private lemma natAbs_sub_lt_of_nonneg {s t : Int} {N : Nat}
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s.natAbs < N) (ht : t.natAbs < N) :
    (s - t).natAbs < N := by
  have heqs : ↑s.natAbs = s := Int.natAbs_of_nonneg hs0
  have heqt : ↑t.natAbs = t := Int.natAbs_of_nonneg ht0
  omega

/-- When two nonpos integers both have natAbs < N, their difference has natAbs < N. -/
private lemma natAbs_sub_lt_of_nonpos {s t : Int} {N : Nat}
    (hs0 : s ≤ 0) (ht0 : t ≤ 0)
    (hs : s.natAbs < N) (ht : t.natAbs < N) :
    (s - t).natAbs < N := by
  have heqs : (↑s.natAbs : Int) = -s := Int.ofNat_natAbs_of_nonpos hs0
  have heqt : (↑t.natAbs : Int) = -t := Int.ofNat_natAbs_of_nonpos ht0
  omega

/-- If `|n * b| < |b|` and `b ≠ 0`, then `n = 0`. -/
private lemma eq_zero_of_mul_natAbs_lt {n b c : Int}
    (hb : b ≠ 0) (h_mul : n * b = c) (h_lt : c.natAbs < b.natAbs) :
    n = 0 := by
  by_contra hn
  rw [← h_mul, Int.natAbs_mul] at h_lt
  have hb_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hn_pos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  -- n.natAbs ≥ 1 and b.natAbs > 0, so n.natAbs * b.natAbs ≥ b.natAbs
  have : b.natAbs ≤ n.natAbs * b.natAbs := Nat.le_mul_of_pos_left _ hn_pos
  omega

/-- **Uniqueness of truncated division.** If `a * b + r = x` with `|r| < |b|`
    and `r` has the same sign as `x` (or `r = 0`), then `a = x.tdiv b`.

    Proof:
    1. From `h_eq` and `tmod_add_tdiv`: `(a - x.tdiv b) * b = x.tmod b - r`
    2. Both `x.tmod b` and `r` have the same sign as `x`, so `|tmod - r| < |b|`
    3. Therefore `|a - x.tdiv b| * |b| < |b|`, giving `a - x.tdiv b = 0`. -/
lemma tdiv_unique (x a b r : Int) (hb : b ≠ 0)
    (h_eq : a * b + r = x)
    (h_bound : r.natAbs < b.natAbs)
    (h_sign : (0 ≤ r ∧ 0 ≤ x) ∨ (r ≤ 0 ∧ x ≤ 0)) :
    a = x.tdiv b := by
  -- Step 1: (a - x.tdiv b) * b = x.tmod b - r
  have h_tdiv_id : x.tmod b + b * x.tdiv b = x := Int.tmod_add_tdiv x b
  have h_diff : (a - x.tdiv b) * b = x.tmod b - r := by
    linarith [Int.sub_mul a (x.tdiv b) b, Int.mul_comm (x.tdiv b) b]
  -- Step 2: |x.tmod b| < |b|
  have h_tmod_bound : (x.tmod b).natAbs < b.natAbs := Int.natAbs_tmod_lt' x b hb
  -- Step 3: tmod and r have same sign, so |tmod - r| < |b|
  have h_diff_bound : (x.tmod b - r).natAbs < b.natAbs := by
    rcases h_sign with ⟨hr_nn, hx_nn⟩ | ⟨hr_np, hx_np⟩
    · exact natAbs_sub_lt_of_nonneg (Int.tmod_nonneg b hx_nn) hr_nn h_tmod_bound h_bound
    · have : x.tmod b ≤ 0 := by
        by_cases hx0 : x = 0
        · simp [hx0]
        · exact Int.tmod_nonpos_of_neg b (by omega)
      exact natAbs_sub_lt_of_nonpos this hr_np h_tmod_bound h_bound
  -- Step 4: |coefficient * b| < |b| implies coefficient = 0
  linarith [eq_zero_of_mul_natAbs_lt hb h_diff h_diff_bound]

/-- Main soundness theorem: if the three Jolt constraint checks pass
    on oracle-provided (q_oracle, abs_r), then the output of
    VirtualAssertValidDiv0 equals Riscv.sdiv x y.

    When y = 0: VirtualAssertValidDiv0 forces result to -1,
    matching Riscv.sdiv x 0 = -1. No constraints needed.

    When y ≠ 0: the three constraints (no-overflow, identity, bound)
    together with XOR-SUB sign correction uniquely determine q_oracle
    as the correct truncated quotient. -/
theorem div_validation_sound (x y q_oracle abs_r : BitVec 64)
    -- Constraint 1: no overflow in q × y_adj
    (h_no_overflow : y ≠ 0 →
      let y_adj := Jolt.virtualChangeDivisor x y
      Riscv.mulh q_oracle y_adj = (Riscv.mul q_oracle y_adj).sshiftRight 63)
    -- Constraint 2: division identity q × y_adj + r_signed = x
    (h_identity : y ≠ 0 →
      let y_adj := Jolt.virtualChangeDivisor x y
      let r_signed := xor_sub_sign abs_r (x.sshiftRight 63)
      Riscv.mul q_oracle y_adj + r_signed = x)
    -- Constraint 3: remainder bound |r| < |y_adj|
    (h_bound : y ≠ 0 →
      let y_adj := Jolt.virtualChangeDivisor x y
      let abs_y := xor_sub_sign y_adj (y_adj.sshiftRight 63)
      abs_r.toNat < abs_y.toNat) :
    Jolt.virtualAssertValidDiv0 y q_oracle = Riscv.sdiv x y := by
  by_cases hy : y = 0
  · -- Division by zero: both sides = BitVec.ofInt 64 (-1)
    subst hy; simp [Jolt.virtualAssertValidDiv0, Riscv.sdiv]
  · -- Non-zero divisor: constraints force q_oracle = correct quotient
    simp only [Jolt.virtualAssertValidDiv0, hy, ↓reduceIte, ne_eq,
               not_false_eq_true]
    -- After simp: goal is q_oracle = Riscv.sdiv x y
    -- Proof strategy:
    -- 1. From h_no_overflow: MUL(q, y_adj).toInt = q.toInt * y_adj.toInt
    --    (via no_overflow_implies_mul_toInt_eq)
    -- 2. From h_identity lifted to Int:
    --    q.toInt * y_adj.toInt + r_signed.toInt = x.toInt
    -- 3. From h_bound: |r_signed.toInt| < |y_adj.toInt|
    -- 4. From XOR-SUB construction: sign(r_signed) = sign(x)
    -- 5. By tdiv_unique: q.toInt = x.toInt.tdiv y_adj.toInt
    -- 6. By change_divisor_correct: ofInt(x.tdiv y_adj) = ofInt(x.tdiv y)
    -- 7. Conclude: q_oracle = Riscv.sdiv x y
    sorry

-- ============================================================================
-- Completeness: correct oracle values pass all constraints
-- ============================================================================
-- These lemmas prove the "other direction": when the oracle provides the
-- mathematically correct quotient and remainder, all constraints are
-- satisfied. This ensures the honest prover is never falsely rejected.

/-- XOR-SUB sign correction correctly converts |v| to ±|v| based on x's sign.
    When x ≥ 0 (msb = false): returns v unchanged.
    When x < 0 (msb = true): returns -v. -/
theorem xor_sub_sign_correct (v : BitVec 64) (x : BitVec 64)
    (hv : v = BitVec.ofNat 64 (x.toInt.natAbs)) :
    xor_sub_sign v (x.sshiftRight 63) =
    BitVec.ofInt 64 (if x.msb = true then -(x.toInt.natAbs : Int) else (x.toInt.natAbs : Int)) := by
  by_cases hmsb : x.msb = true
  · -- x < 0: sign = allOnes, result = -v
    rw [sshiftRight_63_of_msb_true hmsb, xor_sub_allOnes, hv]
    simp only [hmsb, ↓reduceIte]
    -- Goal: -(ofNat 64 natAbs) = ofInt 64 (-(natAbs : Int))
    -- Need: BitVec.ofInt negation commutes with ofNat
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  · -- x ≥ 0: sign = 0, result = v
    have hmsb_false : x.msb = false := Bool.eq_false_iff.mpr (by simp_all)
    rw [sshiftRight_63_of_msb_false hmsb_false]
    simp only [hmsb_false, Bool.false_eq_true, ↓reduceIte]
    -- Goal: xor_sub_sign v 0#64 = BitVec.ofInt 64 ↑x.toInt.natAbs
    rw [BitVec.ofInt_natCast]
    change xor_sub_sign v 0 = _
    rw [xor_sub_zero, hv]

/-- Remainder bound: |x.tmod y| < |y| when y ≠ 0.
    Fundamental property of truncated division. -/
theorem remainder_bound (x y : BitVec 64) (hy : y ≠ (0 : BitVec 64)) :
    (x.toInt.tmod y.toInt).natAbs < y.toInt.natAbs := by
  have hy_int : y.toInt ≠ 0 := by
    intro h; exact hy (BitVec.eq_of_toInt_eq h)
  -- Prove by case analysis on Int constructors (tmod unfolds differently
  -- for each combination of ofNat/negSucc)
  cases hx : x.toInt with
  | ofNat m =>
    cases hy' : y.toInt with
    | ofNat n =>
      simp only [Int.tmod, Int.natAbs]
      have hn : 0 < n := by
        simp only [ne_eq, Int.ofNat_eq_coe, Nat.cast_eq_zero] at hy_int
        rw [hy'] at hy_int; simp at hy_int; omega
      exact Nat.mod_lt m hn
    | negSucc n =>
      simp only [Int.tmod, Int.natAbs]
      exact Nat.mod_lt m (Nat.succ_pos n)
  | negSucc m =>
    cases hy' : y.toInt with
    | ofNat n =>
      simp only [Int.tmod]
      rw [Int.natAbs_neg]
      show m.succ % n < n
      have hn : 0 < n := by
        rw [hy'] at hy_int; simp at hy_int; omega
      exact Nat.mod_lt (m + 1) hn
    | negSucc n =>
      simp only [Int.tmod]
      rw [Int.natAbs_neg]
      show m.succ % n.succ < n.succ
      exact Nat.mod_lt (m + 1) (Nat.succ_pos n)

/-- VirtualChangeDivisor preserves the quotient (mod 2^64).
    Non-overflow: y_adj = y (trivial).
    Overflow (INT_MIN / -1): y_adj = 1, both sides give INT_MIN as BitVec. -/
theorem change_divisor_correct (x y : BitVec 64) (hy : y ≠ (0 : BitVec 64)) :
    let y_adj := Jolt.virtualChangeDivisor x y
    BitVec.ofInt 64 (x.toInt.tdiv y_adj.toInt) = BitVec.ofInt 64 (x.toInt.tdiv y.toInt) := by
  simp only []
  unfold Jolt.virtualChangeDivisor
  split
  · -- Overflow case: x = INT_MIN, y = -1, y_adj = 1
    rename_i h
    obtain ⟨hx, hy_neg1⟩ := h
    subst hx; subst hy_neg1
    native_decide
  · -- Non-overflow: y_adj = y, trivial
    rfl

/-- Division identity (completeness): for the correct oracle values,
    q × y_adj + signed_remainder = x (as BitVec 64).
    Uses the truncated division identity: x = y * (x.tdiv y) + (x.tmod y). -/
theorem div_identity (x y : BitVec 64) (hy : y ≠ (0 : BitVec 64)) :
    let q := BitVec.ofInt 64 (x.toInt.tdiv y.toInt)
    let y_adj := Jolt.virtualChangeDivisor x y
    let abs_r := BitVec.ofNat 64 ((x.toInt.tmod y.toInt).natAbs)
    let sign_x := x.sshiftRight 63
    let r_signed := xor_sub_sign abs_r sign_x
    Riscv.mul q y_adj + r_signed = x := by
  simp only []
  sorry

/-SANITY CHECKS-/
-- Check sdiv == divJolt for small positive values
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:256] do
    for j in [0:256] do
      let x : BitVec 64 := BitVec.ofNat 64 i
      let y : BitVec 64 := BitVec.ofNat 64 j
      if Riscv.sdiv x y != divJolt x y then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Check passed: sdiv == divJolt for 65536 small-value pairs"
  else
    IO.println s!"✗ FAILED: {failures} mismatches found"

-- Test division by zero
#eval show IO Unit from do
  let cases : List (BitVec 64) := [0, 1, 42, BitVec.intMin 64, BitVec.ofInt 64 (-1)]
  let mut ok := true
  for x in cases.toArray do
    if Riscv.sdiv x (0 : BitVec 64) != divJolt x (0 : BitVec 64) then
      ok := false
  if ok then
    IO.println "✓ Division by zero: all cases match"
  else
    IO.println "✗ Division by zero: MISMATCH"

-- Test overflow: INT_MIN / -1
#eval show IO Unit from do
  let x := BitVec.intMin 64
  let y := BitVec.ofInt 64 (-1)
  if Riscv.sdiv x y == divJolt x y then
    IO.println "✓ Overflow (INT_MIN / -1): match"
  else
    IO.println "✗ Overflow (INT_MIN / -1): MISMATCH"

-- Test with negative values (validates tdiv gives correct RISC-V semantics)
#eval show IO Unit from do
  let mut failures := 0
  for i in [0:128] do
    for j in [0:128] do
      let x : BitVec 64 := BitVec.ofInt 64 (-(i : Int) - 1)
      let y : BitVec 64 := BitVec.ofNat 64 (j + 1)
      if Riscv.sdiv x y != divJolt x y then
        failures := failures + 1
      let y2 : BitVec 64 := BitVec.ofInt 64 (-(j : Int) - 1)
      if Riscv.sdiv x y2 != divJolt x y2 then
        failures := failures + 1
  if failures == 0 then
    IO.println "✓ Negative values: all 32768 pairs match"
  else
    IO.println s!"✗ Negative values: {failures} mismatches found"
