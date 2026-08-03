import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Pure BitVec/Int lemmas supporting the DIV proof

Mathematical content that underpins the assertion-guard arguments in
`divProgram_concrete`. Kept separate from `Div.lean` so that
monadic/plumbing content and pure arithmetic content don't sit in the
same file.

Contents:

* **Honest-advice value functions** (`sail_div_value`, `sail_rem_value`):
  verbatim transcriptions of `execute_DIV` / `execute_REM`'s pure bodies
  from the Sail→Lean transpilation. These define what "honest quotient"
  and "honest remainder" mean — what the trusted side would compute.

* **`bv_abs`**: signed absolute value on `BitVec 64`.

* **`v3_eq_v5_of_honest`**: the overflow-fit bridge (Step 8's guard).

* **Four assertion-guard lemmas** — `hguard_div0_of_honest`,
  `hguard_overflow_of_honest`, `hguard_quotient_product_of_honest`,
  `hguard_rem_bound_of_honest` — showing that each assertion's guard
  holds under honest advice. Consumed by `divProgram_concrete` in
  `Div.lean`.
-/

-- ----------------------------------------------------------------------------
-- Honest-advice value functions + absolute value
-- ----------------------------------------------------------------------------

/-- The pure 64-bit value `execute_DIV rs2 rs1 rd is_unsigned` writes to
`rd`, given the values read from `rs1` and `rs2`. Verbatim copy of the
`execute_DIV` body (minus the monadic read/write/return wrapper),
transcribed from `LeanRV64D/InstsEnd.lean:71105`. -/
def sail_div_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (LeanRV64D.Functions.xlen -i 1))) else quotient
  to_bits_truncate (l := 64) quotient

/-- The pure 64-bit value `execute_REM rs2 rs1 rd is_unsigned` writes to
`rd`. Verbatim copy of the `execute_REM` body, transcribed from
`LeanRV64D/InstsEnd.lean:67637`. -/
def sail_rem_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  to_bits_truncate (l := 64) remainder

/-- Absolute value of a signed 64-bit bit-vector: `-x` when the MSB is
set, `x` otherwise. The oracle provides `|remainder|` rather than the
signed remainder, so the `rem_abs` advice is `bv_abs ∘ sail_rem_value`. -/
def bv_abs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

/-- **Step 8 guard (`VirtualAssertEQ v3 v5`) — the overflow check lemma.**

Under honest advice in the *non-overflow* case, the signed product
`q × b` fits in 64 bits, hence its upper half `MULH(q, b)` equals the
sign-broadcast of its lower half `SRAI(MUL(q, b), 63)`.

Assumptions encode:
* `VirtualAssertValidDiv0` did not fire:  `b ≠ 0`.
* `VirtualChangeDivisor` produced `b` (not `a`) into `v2`: no signed
  overflow pair.
* `q` is the honest signed truncating quotient of `a` by `b`.
* `r` is the corresponding remainder satisfying `a = q·b + r` and
  `|r| < |b|`. -/
theorem v3_eq_v5_of_honest
    (a b q r : BitVec 64)
    (hb_ne    : b ≠ 0#64)
    (hno_ovf  : ¬ (a = (1 : BitVec 64) <<< 63 ∧ b = -1))
    (hq       : q = BitVec.sdiv a b)
    (hr       : a = q * b + r)
    (hr_small : r.toInt.natAbs < b.toInt.natAbs) :
    mulhs q b = (q * b).sshiftRight 63 := by
  -- Step 1 — HONEST-ADVICE FIT BOUND.
  --   Under honest signed truncating division (hq), with |r|<|b| (hr_small),
  --   and excluding the signed-overflow pair (hno_ovf), the integer product
  --   q.toInt * b.toInt lies in [-2^63, 2^63).
  have hfits : -(2^63 : Int) ≤ q.toInt * b.toInt ∧ q.toInt * b.toInt < 2^63 := by
    have hshift_eq_intMin : ((1 : BitVec 64) <<< 63) = BitVec.intMin 64 := by decide
    have hneg_eq : ((-1 : BitVec 64)) = (-1#64) := by decide
    have hne_pair : a ≠ BitVec.intMin 64 ∨ b ≠ -1#64 := by
      by_cases ha : a = BitVec.intMin 64
      · right
        intro hb
        apply hno_ovf
        refine ⟨?_, ?_⟩
        · rw [hshift_eq_intMin]; exact ha
        · rw [hneg_eq]; exact hb
      · left; exact ha
    have hqInt : q.toInt = a.toInt.tdiv b.toInt := by
      rw [hq]
      exact BitVec.toInt_sdiv_of_ne_or_ne a b hne_pair
    have hprod_eq : q.toInt * b.toInt = a.toInt - a.toInt.tmod b.toInt := by
      rw [hqInt]
      have := Int.tdiv_mul_self a.toInt b.toInt
      linarith
    have ha_hi : a.toInt < 2^63 := by
      have := @BitVec.toInt_lt 64 a
      simpa using this
    have ha_lo : -(2^63 : Int) ≤ a.toInt := by
      have := @BitVec.le_toInt 64 a
      simpa using this
    have hb_hi : b.toInt < 2^63 := by
      have := @BitVec.toInt_lt 64 b
      simpa using this
    have hb_lo : -(2^63 : Int) ≤ b.toInt := by
      have := @BitVec.le_toInt 64 b
      simpa using this
    have hbInt_ne : b.toInt ≠ 0 := by
      intro h
      apply hb_ne
      apply BitVec.eq_of_toInt_eq
      simpa using h
    have hmod_abs_lt : (a.toInt.tmod b.toInt).natAbs < b.toInt.natAbs := by
      rw [Int.natAbs_tmod]
      exact Nat.mod_lt _ (Int.natAbs_pos.mpr hbInt_ne)
    have hbabs_le : b.toInt.natAbs ≤ (2^63 : Nat) := by
      have h : (b.toInt.natAbs : Int) ≤ (2^63 : Int) := by
        by_cases hbs : 0 ≤ b.toInt
        · rw [Int.natAbs_of_nonneg hbs]; omega
        · push_neg at hbs
          have hnn : 0 ≤ -b.toInt := by omega
          have hn_eq : (b.toInt.natAbs : Int) = -b.toInt := by
            have := Int.natAbs_of_nonneg hnn
            rw [Int.natAbs_neg] at this
            exact this
          rw [hn_eq]; omega
      exact_mod_cast h
    have hmod_abs_bound : (a.toInt.tmod b.toInt).natAbs ≤ (2^63 - 1 : Nat) := by
      omega
    have hmod_bound_int : |a.toInt.tmod b.toInt| ≤ (2^63 - 1 : Int) := by
      rw [Int.abs_eq_natAbs]
      have : ((a.toInt.tmod b.toInt).natAbs : Int) ≤ ((2^63 - 1 : Nat) : Int) := by
        exact_mod_cast hmod_abs_bound
      have heq : ((2^63 - 1 : Nat) : Int) = (2^63 - 1 : Int) := by decide
      omega
    have tmod_nonpos : ∀ {x : Int}, x ≤ 0 → Int.tmod x b.toInt ≤ 0 := by
      intro x hx
      have h1 : 0 ≤ -x := by omega
      have h2 : 0 ≤ Int.tmod (-x) b.toInt := Int.tmod_nonneg b.toInt h1
      rw [Int.neg_tmod] at h2
      omega
    refine ⟨?_, ?_⟩
    · rw [hprod_eq]
      by_cases ha_nn : 0 ≤ a.toInt
      · have htmod_nn : 0 ≤ a.toInt.tmod b.toInt :=
          Int.tmod_nonneg b.toInt ha_nn
        have : a.toInt.tmod b.toInt ≤ (2^63 - 1 : Int) := by
          have := abs_le.mp hmod_bound_int
          omega
        omega
      · push_neg at ha_nn
        have htmod_np : a.toInt.tmod b.toInt ≤ 0 := tmod_nonpos (le_of_lt ha_nn)
        omega
    · rw [hprod_eq]
      by_cases ha_nn : 0 ≤ a.toInt
      · have htmod_nn : 0 ≤ a.toInt.tmod b.toInt :=
          Int.tmod_nonneg b.toInt ha_nn
        omega
      · push_neg at ha_nn
        have htmod_np : a.toInt.tmod b.toInt ≤ 0 := tmod_nonpos (le_of_lt ha_nn)
        have : -(2^63 - 1 : Int) ≤ a.toInt.tmod b.toInt := by
          have := abs_le.mp hmod_bound_int
          omega
        omega
  -- Step 2 — no overflow ⇒ (q*b).toInt = q.toInt * b.toInt.
  have htoInt_mul : (q * b).toInt = q.toInt * b.toInt := by
    have hlo := hfits.1
    have hhi := hfits.2
    rw [BitVec.toInt_mul]
    apply Int.bmod_eq_of_le
    · show -(((2 ^ 64 : Nat) : Int) / 2) ≤ q.toInt * b.toInt
      have h : (((2 ^ 64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h]; exact hlo
    · show q.toInt * b.toInt < (((2 ^ 64 : Nat) : Int) + 1) / 2
      have h : ((((2 ^ 64 : Nat) : Int) + 1) / 2) = (2^63 : Int) := by decide
      rw [h]; exact hhi
  -- Step 3 — both sides reduce to `BitVec.ofInt 64` of the same Int.
  unfold mulhs
  rw [BitVec.sshiftRight_eq]
  rw [htoInt_mul]
  congr 1
  rw [Int.shiftRight_eq_div_pow]
  have hlo := hfits.1
  have hhi := hfits.2
  have hcast63 : ((2^63 : Nat) : Int) = (2^63 : Int) := by decide
  rw [hcast63]
  by_cases hxnn : 0 ≤ q.toInt * b.toInt
  · have h1 : q.toInt * b.toInt / (2^64 : Int) = 0 := by
      apply Int.ediv_eq_zero_of_lt hxnn
      have h64 : (2^63 : Int) < (2^64 : Int) := by decide
      omega
    have h2 : q.toInt * b.toInt / (2^63 : Int) = 0 := by
      apply Int.ediv_eq_zero_of_lt hxnn
      exact hhi
    rw [h1, h2]
  · have hxneg : q.toInt * b.toInt < 0 := by omega
    have h1 : q.toInt * b.toInt / (2^64 : Int) = -1 := by
      apply Int.ediv_eq_neg_one_of_neg_of_le hxneg
      have h263 : (2^63 : Int) ≤ (2^64 : Int) := by decide
      omega
    have h2 : q.toInt * b.toInt / (2^63 : Int) = -1 := by
      apply Int.ediv_eq_neg_one_of_neg_of_le hxneg
      omega
    rw [h1, h2]

-- ----------------------------------------------------------------------------
-- Assertion-guard lemmas: each Jolt assertion's guard holds under honest advice
-- ----------------------------------------------------------------------------
-- Each of the four lemmas below closes one of the asserts in `divProgram`,
-- showing that the guard condition follows purely from the fact that
-- the oracle produced the advice Sail would produce. No trust is placed
-- in the oracle beyond "it returned `sail_div_value` / `sail_rem_value`".
--
-- The guards, in order of appearance in the Jolt sequence:
--   1. `VirtualAssertValidDiv0`        — step 3
--   2. `VirtualAssertEQ v3 v5`         — step 8  (overflow check)
--   3. `VirtualAssertEQ v4 rs1`        — step 13 (quotient·divisor + r = dividend)
--   4. `VirtualAssertValidUnsignedRemainder` — step 17 (|r| < |adj|)

-- ============================================================================
-- Round-trip helpers for `to_bits_truncate ∘ BitVec.toInt`
-- ============================================================================
-- 64-bit analogs of `mod33_toNat_mod32` / `trunc32_eq_intCast` from
-- `ALUFamily/Bridges/Mul.lean`. They bridge the Sail transpilation's
-- `to_bits_truncate (l := 64) x` to `BitVec.ofInt 64 x` (the IntCast),
-- which then simp-collapses with `BitVec.ofInt_toInt`.

private theorem mod65_toNat_mod64 (x : Int) :
    (x % 36893488147419103232).toNat % 18446744073709551616
      = (x % 18446744073709551616).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (36893488147419103232 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (18446744073709551616 : Int) ≠ 0))]

private theorem trunc64_eq_intCast (x : Int) :
    to_bits_truncate (l := 64) x = (x : BitVec 64) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 64) x
        = BitVec.ofNat 64 ((x % 36893488147419103232).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod65_toNat_mod64 x

-- ============================================================================
-- Case helpers for sail_div_value / sail_rem_value / bv_abs
-- ============================================================================
/-!
The four `hguard_*_of_honest` lemmas all need to inspect what
`sail_div_value` and `sail_rem_value` return in each branch (zero
divisor, signed-overflow pair, normal case). Pulling those case
reductions into named lemmas — sorried for now — keeps each downstream
proof short and factors the Sail/Mathlib bridge into one place per
case.

* `sail_div_value` cases:
  - `divisor = 0`                                  → returns `-1`.
  - `(dividend, divisor) = (INT_MIN, -1)` (overflow) → returns `INT_MIN`.
  - otherwise (`normal`)                            → returns `BitVec.sdiv`.

* `sail_rem_value` cases:
  - `divisor = 0`                                  → returns `dividend`.
  - otherwise (`normal`)                            → returns `BitVec.srem`.

* General two's-complement identity reused by `hguard_quotient_product`
  and `hguard_rem_bound`:
  - `bv_abs x = (x ^^^ x.sshiftRight 63) - x.sshiftRight 63`.
-/

/-- `sail_div_value` returns `-1` when the divisor is zero. -/
theorem sail_div_value_of_zero (dividend divisor : BitVec 64) (h : divisor = 0#64) :
    sail_div_value dividend divisor false = (-1 : BitVec 64) := by
  subst h
  unfold sail_div_value
  simp
  decide

/-- `sail_div_value` returns `INT_MIN` in the signed-overflow case
`(dividend, divisor) = (INT_MIN, -1)`. -/
theorem sail_div_value_of_overflow (dividend divisor : BitVec 64)
    (h_pair : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1) :
    sail_div_value dividend divisor false = (1 : BitVec 64) <<< 63 := by
  obtain ⟨hd, hdv⟩ := h_pair
  subst hd
  subst hdv
  decide

/-- `sail_div_value` agrees with `BitVec.sdiv` outside the divide-by-zero
and signed-overflow cases. -/
theorem sail_div_value_of_normal (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64)
    (h_no_ovf : ¬ (dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1)) :
    sail_div_value dividend divisor false = BitVec.sdiv dividend divisor := by
  -- Standard prologue: divisor.toInt ≠ 0, and `dividend ≠ INT_MIN ∨ divisor ≠ -1`.
  have hdivInt : divisor.toInt ≠ 0 := by
    intro h; apply h_ne; apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_zero]; exact h
  have hshift_eq_intMin : ((1 : BitVec 64) <<< 63) = BitVec.intMin 64 := by decide
  have hneg_eq : ((-1 : BitVec 64)) = (-1#64) := by decide
  have hne_pair : dividend ≠ BitVec.intMin 64 ∨ divisor ≠ -1#64 := by
    by_cases ha : dividend = BitVec.intMin 64
    · right; intro hb; apply h_no_ovf
      exact ⟨hshift_eq_intMin ▸ ha, hneg_eq ▸ hb⟩
    · left; exact ha
  have hsdivInt : (BitVec.sdiv dividend divisor).toInt
                = dividend.toInt.tdiv divisor.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne dividend divisor hne_pair
  have hbnd_hi : dividend.toInt.tdiv divisor.toInt < 2^63 := by
    rw [← hsdivInt]
    have := @BitVec.toInt_lt 64 (BitVec.sdiv dividend divisor); simpa using this
  -- Resolve the two sail ifs; the second (overflow correction) takes the else.
  unfold sail_div_value
  simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hdivInt,
             show LeanRV64D.Functions.not false = true from rfl, Bool.true_and]
  -- Goal: to_bits_truncate (if Int.tdiv ... ≥b 2^(xlen-1) then -... else Int.tdiv ...) = BitVec.sdiv ...
  have hge_false :
      (dividend.toInt.tdiv divisor.toInt ≥b
        2 ^ ((LeanRV64D.Functions.xlen : Int) - 1)) = false := by
    show decide _ = false
    apply decide_eq_false
    push_neg
    have : (2 : Int) ^ ((LeanRV64D.Functions.xlen : Int) - 1) = 2^63 := by decide
    rw [this]
    exact hbnd_hi
  rw [hge_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Goal: to_bits_truncate (Int.tdiv ...) = BitVec.sdiv ...
  rw [trunc64_eq_intCast, ← hsdivInt]
  exact BitVec.ofInt_toInt

/-- `sail_rem_value` returns the dividend when the divisor is zero. -/
theorem sail_rem_value_of_zero (dividend divisor : BitVec 64) (h : divisor = 0#64) :
    sail_rem_value dividend divisor false = dividend := by
  subst h
  unfold sail_rem_value
  simp only [BitVec.toInt_zero, beq_iff_eq, decide_true, ↓reduceIte]
  rw [trunc64_eq_intCast]
  exact BitVec.ofInt_toInt

/-- `sail_rem_value` agrees with `BitVec.srem` (truncated signed
remainder) when the divisor is nonzero. -/
theorem sail_rem_value_of_normal (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    sail_rem_value dividend divisor false = BitVec.srem dividend divisor := by
  have hdivInt : divisor.toInt ≠ 0 := by
    intro h; apply h_ne; apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_zero]; exact h
  unfold sail_rem_value
  simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hdivInt]
  -- Goal: to_bits_truncate (Int.tmod dividend.toInt divisor.toInt) = BitVec.srem dividend divisor
  rw [trunc64_eq_intCast, ← BitVec.toInt_srem]
  exact BitVec.ofInt_toInt

/-- Sign-broadcast at bit 63: when the msb is clear, `sshiftRight 63`
returns the all-zeros bitvector. -/
private theorem sshiftRight_63_of_msb_false {x : BitVec 64}
    (h : x.msb = false) : x.sshiftRight 63 = 0#64 := by
  rw [BitVec.sshiftRight_eq_of_msb_false h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
  have hx : 2 * x.toNat < 2 ^ 64 := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have : x.toNat / 2^63 = 0 := by omega
  rw [Nat.shiftRight_eq_div_pow]; exact this

/-- Sign-broadcast at bit 63: when the msb is set, `sshiftRight 63`
returns the all-ones bitvector (`= -1`). -/
private theorem sshiftRight_63_of_msb_true {x : BitVec 64}
    (h : x.msb = true) : x.sshiftRight 63 = -1#64 := by
  rw [BitVec.sshiftRight_eq_of_msb_true h]
  have hnotmsb : (~~~x).msb = false := by
    rw [BitVec.msb_not]; simp [h]
  -- `(~~~x).sshiftRight 63 = 0`, and `(~~~x).sshiftRight 63 = (~~~x) >>> 63` by msb-false lemma.
  have hush_zero : (~~~x) >>> 63 = 0#64 := by
    rw [← BitVec.sshiftRight_eq_of_msb_false hnotmsb]
    exact sshiftRight_63_of_msb_false hnotmsb
  rw [hush_zero]
  decide

/-- Inverse of `bv_abs_eq_xor_sub_sign`: applying the sign-fixup XOR-SUB to
`bv_abs x` (with `x`'s own sign-broadcast) recovers `x` itself. Useful in
`hguard_quotient_product_of_honest`'s divisor=0 branch, where the sign-fixup
of `|dividend|` with `dividend`'s sign yields `dividend`. -/
theorem x_eq_bv_abs_xor_sub_sign (x : BitVec 64) :
    (bv_abs x ^^^ x.sshiftRight 63) - x.sshiftRight 63 = x := by
  unfold bv_abs
  by_cases hmsb : x.msb = true
  · rw [if_pos hmsb, sshiftRight_63_of_msb_true hmsb]
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes]
    -- Goal: ~~~(-x) - allOnes 64 = x
    rw [show BitVec.allOnes 64 = -1#64 from by decide, BitVec.sub_neg]
    -- Goal: ~~~(-x) + 1#64 = x; rewrite via `← neg_eq_not_add` then `neg_neg`.
    rw [← BitVec.neg_eq_not_add, neg_neg]
  · have hf : x.msb = false := by cases h : x.msb; rfl; exact (hmsb h).elim
    rw [if_neg hmsb, sshiftRight_63_of_msb_false hf, BitVec.xor_zero, BitVec.sub_zero]

/-- Two's-complement absolute value identity: `(x ^^^ sign(x)) - sign(x) = |x|`,
where `sign(x) = x.sshiftRight 63` is the sign-broadcast (all-zeros for
non-negative `x`, all-ones for negative `x`). Used to fold the Jolt
sign-fixup expression into `bv_abs` in `hguard_quotient_product` and
`hguard_rem_bound`. -/
theorem bv_abs_eq_xor_sub_sign (x : BitVec 64) :
    bv_abs x = (x ^^^ x.sshiftRight 63) - x.sshiftRight 63 := by
  unfold bv_abs
  by_cases hmsb : x.msb = true
  · -- msb = true: sshiftRight 63 = -1; bv_abs x = -x.
    rw [if_pos hmsb, sshiftRight_63_of_msb_true hmsb]
    -- Goal: -x = (x ^^^ -1#64) - -1#64
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes]
    -- Goal: -x = ~~~x - allOnes 64. Since allOnes = -1 and ~~~x + 1 = -x,
    -- we have ~~~x - (-1) = ~~~x + 1 = -x.
    rw [show BitVec.allOnes 64 = -1#64 from by decide,
        BitVec.sub_neg, BitVec.neg_eq_not_add]
  · -- msb = false: sshiftRight 63 = 0; bv_abs x = x.
    rw [if_neg hmsb]
    have hf : x.msb = false := by
      cases h : x.msb
      · rfl
      · exact (hmsb h).elim
    rw [sshiftRight_63_of_msb_false hf, BitVec.xor_zero, BitVec.sub_zero]

/-- BitVec division equation: `x = (x.sdiv y) * y + x.srem y`. The BitVec
analog of `Int.tmod_add_mul_tdiv`; holds for every input pair, including
`y = 0` and the signed-overflow pair (in those cases the modular wrap of
`BitVec.mul`/`BitVec.add` makes both sides agree on `x`). Proved by
transferring to `Int` via `BitVec.toInt_*`, peeling the `bmod`s with
`Int.bmod_mul_bmod`/`bmod_add_bmod`, applying `Int.tmod_add_mul_tdiv`,
and noting `x.toInt` is already in the canonical bmod range. -/
theorem BitVec.sdiv_mul_add_srem (x y : BitVec 64) :
    x = BitVec.sdiv x y * y + BitVec.srem x y := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_mul, BitVec.toInt_sdiv, BitVec.toInt_srem]
  rw [Int.bmod_mul_bmod, Int.bmod_add_bmod]
  rw [show x.toInt.tdiv y.toInt * y.toInt
        = y.toInt * x.toInt.tdiv y.toInt from Int.mul_comm _ _]
  rw [show y.toInt * x.toInt.tdiv y.toInt + x.toInt.tmod y.toInt
        = x.toInt.tmod y.toInt + y.toInt * x.toInt.tdiv y.toInt from Int.add_comm _ _]
  rw [Int.tmod_add_mul_tdiv]
  -- Goal: x.toInt = x.toInt.bmod (2^64)
  have hlo : -(2^63 : Int) ≤ x.toInt := by
    have := @BitVec.le_toInt 64 x; simpa using this
  have hhi : x.toInt < (2^63 : Int) := by
    have := @BitVec.toInt_lt 64 x; simpa using this
  have hbmod : x.toInt.bmod (2^64) = x.toInt := by
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤ x.toInt
      have h : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h]; exact hlo
    · show x.toInt < ((((2^64 : Nat) : Int) + 1) / 2)
      have h : ((((2^64 : Nat) : Int) + 1) / 2) = (2^63 : Int) := by decide
      rw [h]; exact hhi
  rw [hbmod]

/-- Sign-fixup recovery for `BitVec.srem`: when `divisor ≠ 0`, the Jolt
sign-fixup (XOR with `dividend`'s sign-broadcast, then subtract that sign-
broadcast) of `bv_abs (BitVec.srem dividend divisor)` recovers
`BitVec.srem dividend divisor` itself. This relies on the RISC-V truncated-
remainder convention `sign(srem) = sign(dividend)` (when `srem ≠ 0`), which
makes `srem.sshiftRight 63 = dividend.sshiftRight 63`. -/
theorem srem_xor_sub_sign_eq_srem
    (dividend divisor : BitVec 64) (h_ne : divisor ≠ 0#64) :
    (bv_abs (BitVec.srem dividend divisor) ^^^ dividend.sshiftRight 63)
      - dividend.sshiftRight 63
    = BitVec.srem dividend divisor := by
  by_cases hzero : BitVec.srem dividend divisor = 0#64
  · rw [hzero]
    rw [show bv_abs (0#64 : BitVec 64) = 0#64 from by decide]
    rw [BitVec.zero_xor, BitVec.sub_self]
  · -- srem ≠ 0: msb(srem) = msb(dividend), so the sign-broadcasts agree.
    have hmsb_eq : (BitVec.srem dividend divisor).msb = dividend.msb := by
      rw [BitVec.msb_srem]
      simp [hzero]
    have hssr_eq :
        (BitVec.srem dividend divisor).sshiftRight 63 = dividend.sshiftRight 63 := by
      by_cases hd : dividend.msb = true
      · have hsrem_msb : (BitVec.srem dividend divisor).msb = true :=
          hmsb_eq.trans hd
        rw [sshiftRight_63_of_msb_true hsrem_msb, sshiftRight_63_of_msb_true hd]
      · have hd_f : dividend.msb = false := by
          cases h : dividend.msb; rfl; exact (hd h).elim
        have hsrem_f : (BitVec.srem dividend divisor).msb = false :=
          hmsb_eq.trans hd_f
        rw [sshiftRight_63_of_msb_false hsrem_f, sshiftRight_63_of_msb_false hd_f]
    rw [← hssr_eq]
    exact x_eq_bv_abs_xor_sub_sign (BitVec.srem dividend divisor)

/-- Bridging `bv_abs` (BitVec absolute value) to `Int.natAbs`: the unsigned
size of `bv_abs x` equals the integer absolute value of `x.toInt`. The two
sides agree on every input, including `INT_MIN` (where both are `2^63`). -/
theorem bv_abs_toNat_eq_natAbs (x : BitVec 64) :
    (bv_abs x).toNat = x.toInt.natAbs := by
  -- `bv_abs = BitVec.abs` definitionally, so reuse Mathlib's `BitVec.toNat_abs`.
  rw [show bv_abs x = BitVec.abs x from rfl, BitVec.toNat_abs]
  rw [BitVec.toInt_eq_toNat_cond]
  have hxlt : x.toNat < 2^64 := x.isLt
  by_cases hmsb : x.msb = true
  · rw [if_pos hmsb]
    have hge : 2 * x.toNat ≥ 2^64 := BitVec.msb_eq_true_iff_two_mul_ge.mp hmsb
    rw [if_neg (by omega)]
    -- Goal: 2^64 - x.toNat = ((x.toNat : Int) - 2^64).natAbs
    omega
  · have hf : x.msb = false := by cases h : x.msb; rfl; exact (hmsb h).elim
    rw [if_neg hmsb]
    have hlt : 2 * x.toNat < 2^64 := BitVec.msb_eq_false_iff_two_mul_lt.mp hf
    rw [if_pos hlt]
    -- Goal: x.toNat = ((x.toNat : Int)).natAbs
    omega

-- ============================================================================
-- Assertion-guard lemmas (cont'd)
-- ============================================================================

/-- **Guard 1 — `VirtualAssertValidDiv0`.**

When the divisor is zero, the RISC-V spec fixes the quotient as `-1`
(all ones). Sail implements this in the first branch of `sail_div_value`:
if `rs2_int = 0` it returns `-1` directly, skipping the division. So
under honest advice `q = sail_div_value dividend divisor false`, the
conjunction `divisor = 0 ∧ q ≠ -1` is impossible — the assert guard
holds vacuously in the `divisor = 0` case and trivially when
`divisor ≠ 0`. -/
theorem hguard_div0_of_honest (dividend divisor : BitVec 64) :
    ¬ (divisor = 0#64 ∧
       sail_div_value dividend divisor false ≠ (-1 : BitVec 64)) := by
  rintro ⟨hd, hq⟩
  apply hq
  subst hd
  unfold sail_div_value
  simp
  decide

/-- **Guard 2 — `VirtualAssertEQ v3 v5` (overflow check).**

Under honest advice, the signed product `q · adj_divisor` fits inside
64 bits, so the upper 64 bits (`MULH`) equal the sign-broadcast of the
lower 64 bits (`SRAI` by 63). The core content — "the product fits in
64 bits signed" — is `v3_eq_v5_of_honest` above; this wrapper plugs in
the honest-advice values so the guard appears in exactly the shape the
Phase 2 run-helper expects. -/
theorem hguard_overflow_of_honest (dividend divisor : BitVec 64) :
    let q   := sail_div_value dividend divisor false
    let adj := change_divisor_value dividend divisor
    mulhs q adj = (q * adj).sshiftRight 63 := by
  intro q adj
  by_cases h_zero : divisor = 0#64
  · -- divisor = 0: q = -1, adj = 0; both sides reduce to 0.
    have hq : q = -1#64 := sail_div_value_of_zero dividend divisor h_zero
    have hadj : adj = 0#64 := by
      show change_divisor_value dividend divisor = 0#64
      unfold change_divisor_value
      rw [h_zero]
      simp
    rw [hq, hadj]
    decide
  · by_cases h_ovf : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1
    · -- Overflow: q = INT_MIN, adj = 1; both sides reduce to -1.
      have hq : q = (1 : BitVec 64) <<< 63 :=
        sail_div_value_of_overflow dividend divisor h_ovf
      have hadj : adj = (1 : BitVec 64) := by
        show change_divisor_value dividend divisor = 1
        unfold change_divisor_value
        rw [if_pos h_ovf]
      rw [hq, hadj]
      decide
    · -- Normal: q = BitVec.sdiv, adj = divisor; apply `v3_eq_v5_of_honest`.
      have hq : q = BitVec.sdiv dividend divisor :=
        sail_div_value_of_normal dividend divisor h_zero h_ovf
      have hadj : adj = divisor := by
        show change_divisor_value dividend divisor = divisor
        unfold change_divisor_value
        rw [if_neg h_ovf]
      rw [hq, hadj]
      have hr : dividend = BitVec.sdiv dividend divisor * divisor +
                  BitVec.srem dividend divisor :=
        BitVec.sdiv_mul_add_srem dividend divisor
      have hr_small :
          (BitVec.srem dividend divisor).toInt.natAbs < divisor.toInt.natAbs := by
        rw [BitVec.toInt_srem, Int.natAbs_tmod]
        have hdivInt : divisor.toInt ≠ 0 := by
          intro h; apply h_zero; apply BitVec.eq_of_toInt_eq
          rw [BitVec.toInt_zero]; exact h
        exact Nat.mod_lt _ (Int.natAbs_pos.mpr hdivInt)
      exact v3_eq_v5_of_honest dividend divisor (BitVec.sdiv dividend divisor)
        (BitVec.srem dividend divisor) h_zero h_ovf rfl hr hr_small

/-- **Guard 3 — `VirtualAssertEQ v4 rs1` (division equation).**

The heart of the DIV check: after reconstructing the signed remainder
from `|rem|` and the sign of the dividend (via `XOR + SUB`), the sum
`q · adj + signed_rem` equals the dividend. Under honest advice, where
`q = sail_div_value dividend divisor` and `rem = bv_abs sail_rem_value`,
this is the standard division equation `a = q·b + r`, adapted through
`VirtualChangeDivisor`'s overflow fix-up.

The equation as Jolt's arithmetic sees it:
`q · adj + (rem XOR sign(dividend)) - sign(dividend) = dividend`. -/
theorem hguard_quotient_product_of_honest (dividend divisor : BitVec 64) :
    let q   := sail_div_value dividend divisor false
    let rem := bv_abs (sail_rem_value dividend divisor false)
    let adj := change_divisor_value dividend divisor
    q * adj +
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
      = dividend := by
  intro q rem adj
  by_cases h_zero : divisor = 0#64
  · -- divisor = 0: q = -1, adj = 0, sail_rem = dividend; signed-rem recovers dividend.
    have hq : q = -1#64 := sail_div_value_of_zero dividend divisor h_zero
    have hadj : adj = 0#64 := by
      show change_divisor_value dividend divisor = 0#64
      unfold change_divisor_value; rw [h_zero]; simp
    have hrem : rem = bv_abs dividend := by
      show bv_abs (sail_rem_value dividend divisor false) = _
      rw [sail_rem_value_of_zero dividend divisor h_zero]
    rw [hq, hadj, hrem]
    -- Goal: -1 * 0 + (bv_abs d ^^^ d.sshiftRight 63 - d.sshiftRight 63) = d
    rw [BitVec.mul_zero, BitVec.zero_add]
    exact x_eq_bv_abs_xor_sub_sign dividend
  · by_cases h_ovf : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1
    · -- Overflow: q = INT_MIN, adj = 1, sail_rem = 0, rem = 0; both sides reduce to dividend.
      have hq : q = (1 : BitVec 64) <<< 63 :=
        sail_div_value_of_overflow dividend divisor h_ovf
      have hadj : adj = (1 : BitVec 64) := by
        show change_divisor_value dividend divisor = 1
        unfold change_divisor_value; rw [if_pos h_ovf]
      have hsail_rem : sail_rem_value dividend divisor false = 0#64 := by
        rw [sail_rem_value_of_normal dividend divisor h_zero]
        apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_srem, BitVec.toInt_zero]
        obtain ⟨hd, hdv⟩ := h_ovf
        subst hd; subst hdv
        decide
      have hrem : rem = 0#64 := by
        show bv_abs (sail_rem_value dividend divisor false) = _
        rw [hsail_rem]; decide
      rw [hq, hadj, hrem]
      obtain ⟨hd, _⟩ := h_ovf
      subst hd
      decide
    · -- Normal: q = sdiv, adj = divisor, sail_rem = srem.
      have hq : q = BitVec.sdiv dividend divisor :=
        sail_div_value_of_normal dividend divisor h_zero h_ovf
      have hadj : adj = divisor := by
        show change_divisor_value dividend divisor = divisor
        unfold change_divisor_value; rw [if_neg h_ovf]
      have hrem : rem = bv_abs (BitVec.srem dividend divisor) := by
        show bv_abs (sail_rem_value dividend divisor false) = _
        rw [sail_rem_value_of_normal dividend divisor h_zero]
      rw [hq, hadj, hrem]
      -- Goal: sdiv * divisor + (bv_abs(srem) ^^^ d.sshiftRight 63 - d.sshiftRight 63) = d
      rw [srem_xor_sub_sign_eq_srem dividend divisor h_zero]
      -- Goal: sdiv * divisor + srem = d
      exact (BitVec.sdiv_mul_add_srem dividend divisor).symm

/-- **Guard 4 — `VirtualAssertValidUnsignedRemainder`.**

Under honest advice, the unsigned magnitude of the remainder is
strictly less than the unsigned magnitude of the adjusted divisor. The
RISC-V division relation `|r| < |b|` lifts to `|r| < |adj|` because
`VirtualChangeDivisor` only differs from the identity in the single
overflow pair `(dividend = -2^63, divisor = -1)`, where `sail_rem_value
= 0`, so `|r| = 0 < |adj|` trivially.

The expression `adj XOR sign(adj) - sign(adj)` is Jolt's way of
computing `|adj|` with the sign-fixup trick. -/
theorem hguard_rem_bound_of_honest (dividend divisor : BitVec 64) :
    let rem := bv_abs (sail_rem_value dividend divisor false)
    let adj := change_divisor_value dividend divisor
    ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
      rem.toNat < ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat := by
  intro rem adj
  -- Fold the XOR-SUB sign-fixup into `bv_abs adj`.
  rw [← bv_abs_eq_xor_sub_sign]
  -- Goal: bv_abs adj = 0#64 ∨ rem.toNat < (bv_abs adj).toNat
  by_cases h_zero : divisor = 0#64
  · -- divisor = 0 → adj = 0 → bv_abs adj = 0. Left disjunct.
    left
    show bv_abs adj = 0#64
    have hadj0 : adj = 0#64 := by
      show change_divisor_value dividend divisor = 0#64
      unfold change_divisor_value
      rw [h_zero]
      simp
    rw [hadj0]
    decide
  · by_cases h_ovf : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1
    · -- overflow case: adj = 1, sail_rem = 0, so rem = 0 < |adj| = 1. Right disjunct.
      right
      show rem.toNat < (bv_abs adj).toNat
      obtain ⟨hd, hdv⟩ := h_ovf
      subst hd
      subst hdv
      decide
    · -- normal case: adj = divisor, sail_rem = BitVec.srem dividend divisor,
      -- bv_abs(srem).toNat = |srem|.toInt.natAbs < divisor.toInt.natAbs = (bv_abs divisor).toNat.
      right
      show rem.toNat < (bv_abs adj).toNat
      -- Specialise adj and sail_rem via the case helpers.
      have hadj : adj = divisor := by
        show change_divisor_value dividend divisor = divisor
        unfold change_divisor_value
        rw [if_neg h_ovf]
      have hsail :
          sail_rem_value dividend divisor false = BitVec.srem dividend divisor :=
        sail_rem_value_of_normal dividend divisor h_zero
      have hrem_eq : rem = bv_abs (BitVec.srem dividend divisor) := by
        show bv_abs (sail_rem_value dividend divisor false) = _
        rw [hsail]
      rw [hrem_eq, hadj]
      -- Bridge to Int via bv_abs_toNat_eq_natAbs and BitVec.toInt_srem.
      rw [bv_abs_toNat_eq_natAbs, bv_abs_toNat_eq_natAbs]
      -- Goal: (BitVec.srem dividend divisor).toInt.natAbs < divisor.toInt.natAbs
      have hdiv_ne : divisor.toInt ≠ 0 := by
        intro h; apply h_zero
        exact BitVec.eq_of_toInt_eq (by simpa using h)
      rw [BitVec.toInt_srem, Int.natAbs_tmod]
      exact Nat.mod_lt _ (Int.natAbs_pos.mpr hdiv_ne)

-- ----------------------------------------------------------------------------
-- Uniqueness of advice — soundness core
-- ----------------------------------------------------------------------------

/-- Inverting the sign-fixup: given `(rem ^^^ sign(y)) - sign(y) = y`, the only
`rem` solving this equation is `bv_abs y`. The sign-fixup operation
`f(x) = (x ^^^ s) - s` is an involution (since `s ∈ {0, -1}`), so applying
it again recovers the input. -/
private theorem rem_from_sign_fixup_eq (rem y : BitVec 64)
    (h : (rem ^^^ y.sshiftRight 63) - y.sshiftRight 63 = y) :
    rem = bv_abs y := by
  unfold bv_abs
  by_cases hmsb : y.msb = true
  · rw [if_pos hmsb]
    rw [sshiftRight_63_of_msb_true hmsb] at h
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes] at h
    rw [show BitVec.allOnes 64 = -1#64 from by decide, BitVec.sub_neg] at h
    rw [← BitVec.neg_eq_not_add] at h
    -- h : -rem = y;  goal : rem = -y
    rw [BitVec.neg_eq_iff_eq_neg] at h
    exact h
  · have hf : y.msb = false := by cases h' : y.msb; rfl; exact (hmsb h').elim
    rw [if_neg hmsb]
    rw [sshiftRight_63_of_msb_false hf, BitVec.xor_zero, BitVec.sub_zero] at h
    exact h

/-- `BitVec 64` value with `toNat < 1` is `0#64`. -/
private theorem bv_eq_zero_of_toNat_lt_one (x : BitVec 64) (h : x.toNat < 1) :
    x = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp; omega

/-- **Sub-helper #1.** The overflow-check guard `h2` forces the integer
product `q.toInt * b.toInt` to lie in the canonical signed-64-bit range
`[-2^63, 2^63)`. This is the converse content of `v3_eq_v5_of_honest` —
that lemma derives `mulhs q b = (q*b).sshiftRight 63` *from* the
no-overflow bound; here we go the other direction.

Proof strategy: take `.toInt` of both sides of `h`. Compute
`(mulhs q b).toInt = ((q.toInt * b.toInt) / 2^64).bmod (2^64)` and
`((q*b).sshiftRight 63).toInt ∈ {0, -1}` based on `(q*b).msb`. Since
`p / 2^64` is bounded by `±2^62`, the `bmod (2^64) = -1` (resp `= 0`)
forces `p / 2^64 = -1` (resp `= 0`). Combined with `(q*b).msb`'s
constraint on `p.bmod (2^64)`, we get `p ∈ [-2^63, 2^63)`. -/
private theorem product_in_range_of_mulhs_eq {q b : BitVec 64}
    (h : mulhs q b = (q * b).sshiftRight 63) :
    -(2^63 : Int) ≤ q.toInt * b.toInt ∧ q.toInt * b.toInt < 2^63 := by
  -- BitVec toInt bounds.
  have hq_lo : -(2^63 : Int) ≤ q.toInt := by
    have := @BitVec.le_toInt 64 q; simpa using this
  have hq_hi : q.toInt < 2^63 := by
    have := @BitVec.toInt_lt 64 q; simpa using this
  have hb_lo : -(2^63 : Int) ≤ b.toInt := by
    have := @BitVec.le_toInt 64 b; simpa using this
  have hb_hi : b.toInt < 2^63 := by
    have := @BitVec.toInt_lt 64 b; simpa using this
  -- Bounds on p.
  have hp_lo : -(2^126 : Int) ≤ q.toInt * b.toInt := by nlinarith
  have hp_hi : q.toInt * b.toInt ≤ 2^126 := by nlinarith
  -- Bounds on p / 2^64.
  have hediv_lo : -(2^62 : Int) ≤ q.toInt * b.toInt / 2^64 := by
    rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : Int) < 2^64)]; linarith
  have hediv_hi : q.toInt * b.toInt / 2^64 ≤ 2^62 := by
    rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : Int) < 2^64)]; linarith
  -- Take toInt of h.
  have h_int : (mulhs q b).toInt = ((q * b).sshiftRight 63).toInt := by rw [h]
  have hL : (mulhs q b).toInt = ((q.toInt * b.toInt) / 2^64).bmod (2^64) := by
    show (BitVec.ofInt 64 ((q.toInt * b.toInt) / 2^64)).toInt = _
    rw [BitVec.toInt_ofInt]
  rw [hL] at h_int
  -- (q*b).toInt = p.bmod (2^64).
  have hM : (q * b).toInt = (q.toInt * b.toInt).bmod (2^64) := BitVec.toInt_mul q b
  -- Helpers: 2^64/2 = 2^63 and (2^64+1)/2 = 2^63.
  have h64a : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
  have h64b : (((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int) := by decide
  -- Case on (q*b).msb.
  by_cases hmsb : (q * b).msb = true
  · -- msb = true → sshiftRight = -1#64, RHS toInt = -1.
    rw [sshiftRight_63_of_msb_true hmsb] at h_int
    rw [show ((-1#64 : BitVec 64)).toInt = -1 from by decide] at h_int
    -- p / 2^64 = -1.
    have hediv_eq : q.toInt * b.toInt / 2^64 = -1 := by
      have h1 : -(((2^64 : Nat) : Int) / 2) ≤ q.toInt * b.toInt / 2^64 := by
        rw [h64a]; linarith
      have h2 : q.toInt * b.toInt / 2^64 < (((2^64 : Nat) : Int) + 1) / 2 := by
        rw [h64b]; linarith
      rw [Int.bmod_eq_of_le h1 h2] at h_int
      exact h_int
    -- p ∈ [-2^64, 0).
    have hp_ge : -(2^64 : Int) ≤ q.toInt * b.toInt := by
      have : (-1 : Int) * 2^64 ≤ q.toInt * b.toInt := by
        rw [← Int.le_ediv_iff_mul_le (by norm_num : (0 : Int) < 2^64)]; linarith
      linarith
    have hp_lt : q.toInt * b.toInt < 0 := by
      have : q.toInt * b.toInt < 0 * 2^64 := by
        rw [← Int.ediv_lt_iff_lt_mul (by norm_num : (0 : Int) < 2^64)]; linarith
      linarith
    -- (q*b).msb = true → p.bmod (2^64) < 0.
    have hbm_neg : (q.toInt * b.toInt).bmod (2^64) < 0 := by
      have h_qb_neg : (q * b).toInt < 0 := BitVec.toInt_neg_of_msb_true hmsb
      rw [hM] at h_qb_neg; exact h_qb_neg
    -- For p ∈ [-2^64, 0), p.bmod (2^64) < 0 forces p ≥ -2^63.
    refine ⟨?_, by linarith⟩
    -- Use the bmod = x - m*bdiv decomposition; bdiv must be 0 (since p ∈ [-2^64, 0) and bmod < 0).
    have h_bmod_decomp :
        (q.toInt * b.toInt).bmod (2^64)
          = q.toInt * b.toInt - (2^64 : Nat) * (q.toInt * b.toInt).bdiv (2^64) :=
      Int.bmod_eq_self_sub_mul_bdiv _ _
    have h_bmod_lo : -(((2^64 : Nat) : Int) / 2) ≤ (q.toInt * b.toInt).bmod (2^64) :=
      Int.le_bmod (by norm_num)
    have h_bmod_hi :
        (q.toInt * b.toInt).bmod (2^64) < (((2^64 : Nat) : Int) + 1) / 2 :=
      Int.bmod_lt (by norm_num)
    rw [h64a] at h_bmod_lo
    rw [h64b] at h_bmod_hi
    push_cast at h_bmod_decomp
    -- Normalize `2^64` literal across all hypotheses.
    norm_num at *
    omega
  · -- msb = false → sshiftRight = 0#64, RHS toInt = 0.
    have hmsb_f : (q * b).msb = false := by
      cases h' : (q * b).msb; rfl; exact (hmsb h').elim
    rw [sshiftRight_63_of_msb_false hmsb_f] at h_int
    rw [show ((0#64 : BitVec 64)).toInt = 0 from by decide] at h_int
    -- p / 2^64 = 0.
    have hediv_eq : q.toInt * b.toInt / 2^64 = 0 := by
      have h1 : -(((2^64 : Nat) : Int) / 2) ≤ q.toInt * b.toInt / 2^64 := by
        rw [h64a]; linarith
      have h2 : q.toInt * b.toInt / 2^64 < (((2^64 : Nat) : Int) + 1) / 2 := by
        rw [h64b]; linarith
      rw [Int.bmod_eq_of_le h1 h2] at h_int
      exact h_int
    -- p ∈ [0, 2^64).
    have hp_ge : 0 ≤ q.toInt * b.toInt := by
      have : (0 : Int) * 2^64 ≤ q.toInt * b.toInt := by
        rw [← Int.le_ediv_iff_mul_le (by norm_num : (0 : Int) < 2^64)]; linarith
      linarith
    have hp_lt : q.toInt * b.toInt < 2^64 := by
      have : q.toInt * b.toInt < 1 * 2^64 := by
        rw [← Int.ediv_lt_iff_lt_mul (by norm_num : (0 : Int) < 2^64)]; linarith
      linarith
    -- (q*b).msb = false → 0 ≤ p.bmod (2^64).
    have hbm_nn : 0 ≤ (q.toInt * b.toInt).bmod (2^64) := by
      have h_qb_nn : 0 ≤ (q * b).toInt :=
        BitVec.toInt_nonneg_of_msb_false hmsb_f
      rw [hM] at h_qb_nn; exact h_qb_nn
    -- For p ∈ [0, 2^64) with bmod ≥ 0, conclude p < 2^63.
    refine ⟨by linarith, ?_⟩
    -- Same bdiv-decomposition approach.
    have h_bmod_decomp :
        (q.toInt * b.toInt).bmod (2^64)
          = q.toInt * b.toInt - (2^64 : Nat) * (q.toInt * b.toInt).bdiv (2^64) :=
      Int.bmod_eq_self_sub_mul_bdiv _ _
    have h_bmod_lo : -(((2^64 : Nat) : Int) / 2) ≤ (q.toInt * b.toInt).bmod (2^64) :=
      Int.le_bmod (by norm_num)
    have h_bmod_hi :
        (q.toInt * b.toInt).bmod (2^64) < (((2^64 : Nat) : Int) + 1) / 2 :=
      Int.bmod_lt (by norm_num)
    rw [h64a] at h_bmod_lo
    rw [h64b] at h_bmod_hi
    push_cast at h_bmod_decomp
    -- Normalize `2^64` literal across all hypotheses.
    norm_num at *
    omega

/-- **Sub-helper #2.** Convert the BitVec sign-fixup to an `Int` formula
that's easy to feed to `Int.tdiv_tmod_unique`: `signed_rem.toInt` equals
`rem.toNat` (when `dividend.msb = false`) or `-rem.toNat` (when set).
Hypothesis `hrem_msb : rem.msb = false` ensures `rem.toInt = rem.toNat`. -/
private theorem signed_rem_toInt {rem dividend : BitVec 64}
    (hrem_msb : rem.msb = false) :
    ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63).toInt
      = if dividend.msb then -(rem.toNat : Int) else (rem.toNat : Int) := by
  by_cases hd : dividend.msb = true
  · rw [if_pos hd, sshiftRight_63_of_msb_true hd]
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes]
    rw [show BitVec.allOnes 64 = -1#64 from by decide, BitVec.sub_neg]
    rw [← BitVec.neg_eq_not_add]
    -- Goal: (-rem).toInt = -(rem.toNat : Int)
    rw [BitVec.toInt_neg, BitVec.toInt_eq_toNat_of_msb hrem_msb]
    -- Goal: (-(rem.toNat : Int)).bmod (2^64) = -(rem.toNat : Int)
    have h_bound : (rem.toNat : Int) < 2^63 := by
      have : 2 * rem.toNat < 2^64 := BitVec.msb_eq_false_iff_two_mul_lt.mp hrem_msb
      exact_mod_cast (by omega : rem.toNat < 2^63)
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤ -(rem.toNat : Int)
      have h64 : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h64]; omega
    · show -(rem.toNat : Int) < (((2^64 : Nat) : Int) + 1) / 2
      have h64 : (((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int) := by decide
      rw [h64]
      have : 0 ≤ (rem.toNat : Int) := Int.natCast_nonneg _
      omega
  · have hd_f : dividend.msb = false := by
      cases h : dividend.msb
      · rfl
      · exact (hd h).elim
    rw [if_neg hd, sshiftRight_63_of_msb_false hd_f, BitVec.xor_zero, BitVec.sub_zero]
    exact BitVec.toInt_eq_toNat_of_msb hrem_msb

/-- **Sub-helper #3.** The final Int-uniqueness step: given the lifted
identity, the bound, and the sign-condition on `signed_rem.toInt`, we get
`q.toInt = dividend.toInt.tdiv divisor.toInt` and
`signed_rem.toInt = dividend.toInt.tmod divisor.toInt`. Direct application
of `Int.tdiv_tmod_unique` (or its `'` variant). -/
private theorem int_uniqueness_step {a b q r : Int} (hb : b ≠ 0)
    (heq : q * b + r = a)
    (hr_pos : 0 ≤ a → 0 ≤ r)
    (hr_neg : a < 0 → r ≤ 0)
    (hr_lt : r.natAbs < b.natAbs) :
    a.tdiv b = q ∧ a.tmod b = r := by
  by_cases ha : 0 ≤ a
  · refine (Int.tdiv_tmod_unique ha hb).mpr ⟨?_, hr_pos ha, ?_⟩
    · linarith [Int.mul_comm q b]
    · have h1 : (r.natAbs : Int) = r :=
        Int.natAbs_of_nonneg (hr_pos ha)
      have h2 : (r.natAbs : Int) < (b.natAbs : Int) := by exact_mod_cast hr_lt
      omega
  · push_neg at ha
    refine (Int.tdiv_tmod_unique' (le_of_lt ha) hb).mpr ⟨?_, ?_, hr_neg ha⟩
    · linarith [Int.mul_comm q b]
    · have hr_np : r ≤ 0 := hr_neg ha
      have h1 : (r.natAbs : Int) = -r := by
        have h_nn : 0 ≤ -r := by linarith
        have := Int.natAbs_of_nonneg h_nn
        rw [Int.natAbs_neg] at this
        exact this
      have h2 : (r.natAbs : Int) < (b.natAbs : Int) := by exact_mod_cast hr_lt
      omega

/-- Soundness uniqueness in the **normal** case (divisor ≠ 0 and not the
overflow pair). Given the BitVec division equation and the no-overflow
guard h2, plus the bound `rem.toNat < |divisor|.toNat`, the advice
`(q, rem)` is forced to `(BitVec.sdiv dividend divisor,
bv_abs (BitVec.srem dividend divisor))`. The proof routes through Int via
`BitVec.toInt_mul_of_not_smulOverflow` (h2 → no overflow) and
`Int.tdiv_tmod_unique` for the canonical Int uniqueness; then transports
back via `BitVec.toInt_sdiv_of_ne_or_ne` and `bv_abs_toNat_eq_natAbs`. -/
private theorem advice_unique_normal
    (dividend divisor q rem : BitVec 64)
    (h_ne : divisor ≠ 0#64)
    (h_no_ovf : ¬ (dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1))
    (h2 : mulhs q divisor = (q * divisor).sshiftRight 63)
    (h3 : q * divisor +
            ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
          = dividend)
    (hbnd : rem.toNat < divisor.toInt.natAbs) :
    q = BitVec.sdiv dividend divisor ∧
    rem = bv_abs (BitVec.srem dividend divisor) := by
  -- Setup.
  have hdivInt_ne : divisor.toInt ≠ 0 := by
    intro h; apply h_ne; apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_zero]; exact h
  have hshift_eq_intMin : ((1 : BitVec 64) <<< 63) = BitVec.intMin 64 := by decide
  have hneg_eq : ((-1 : BitVec 64)) = (-1#64) := by decide
  have hne_pair : dividend ≠ BitVec.intMin 64 ∨ divisor ≠ -1#64 := by
    by_cases ha : dividend = BitVec.intMin 64
    · right; intro hb; apply h_no_ovf
      exact ⟨hshift_eq_intMin ▸ ha, hneg_eq ▸ hb⟩
    · left; exact ha
  -- divisor.toInt bounds.
  have hdiv_lo : -(2^63 : Int) ≤ divisor.toInt := by
    have := @BitVec.le_toInt 64 divisor; simpa using this
  have hdiv_hi : divisor.toInt < 2^63 := by
    have := @BitVec.toInt_lt 64 divisor; simpa using this
  have hdiv_natAbs_le : divisor.toInt.natAbs ≤ 2^63 := by
    rcases Int.natAbs_eq divisor.toInt with hpos | hneg
    · have h1 : (divisor.toInt.natAbs : Int) ≤ (2^63 : Int) := by rw [← hpos]; omega
      exact_mod_cast h1
    · have h1 : (divisor.toInt.natAbs : Int) = -divisor.toInt := by
        have := Int.natAbs_of_nonneg (show (0 : Int) ≤ -divisor.toInt by omega)
        rw [Int.natAbs_neg] at this; exact this
      have h2 : (divisor.toInt.natAbs : Int) ≤ (2^63 : Int) := by rw [h1]; omega
      exact_mod_cast h2
  -- rem.msb = false.
  have hrem_msb : rem.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    have : rem.toNat < 2^63 := lt_of_lt_of_le hbnd hdiv_natAbs_le
    omega
  -- signed_rem.toInt formula.
  have h_signed_int :
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63).toInt
        = if dividend.msb then -(rem.toNat : Int) else (rem.toNat : Int) :=
    signed_rem_toInt hrem_msb
  -- Product range from h2.
  obtain ⟨h_p_lo, h_p_hi⟩ := product_in_range_of_mulhs_eq h2
  -- (q * divisor).toInt = q.toInt * divisor.toInt (no smulOverflow).
  have h_no_smulOvf : q.smulOverflow divisor = false := by
    unfold BitVec.smulOverflow
    have hp : (2 : Int)^(64 - 1) = 2^63 := by norm_num
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt, hp]
    exact ⟨h_p_hi, h_p_lo⟩
  have h_no_smulOvf' : ¬ q.smulOverflow divisor = true := by
    rw [h_no_smulOvf]; decide
  have h_qdiv_toInt : (q * divisor).toInt = q.toInt * divisor.toInt :=
    BitVec.toInt_mul_of_not_smulOverflow h_no_smulOvf'
  -- Set s := signed_rem.
  set s := (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 with hs_def
  -- |s.toInt| = rem.toNat.
  have h_s_natAbs : s.toInt.natAbs = rem.toNat := by
    rw [h_signed_int]
    by_cases hd : dividend.msb
    · simp [hd, Int.natAbs_neg]
    · simp [hd]
  -- |s.toInt| < |divisor.toInt|.
  have h_s_natAbs_lt : s.toInt.natAbs < divisor.toInt.natAbs := h_s_natAbs ▸ hbnd
  -- s.toInt sign condition: ≥ 0 when dividend.toInt ≥ 0; ≤ 0 when dividend.toInt < 0.
  have h_s_sign_pos : 0 ≤ dividend.toInt → 0 ≤ s.toInt := by
    intro _
    rw [h_signed_int]
    by_cases hdmsb : dividend.msb
    · simp [hdmsb]
      have := BitVec.toInt_neg_of_msb_true hdmsb; omega
    · simp [hdmsb]
  have h_s_sign_neg : dividend.toInt < 0 → s.toInt ≤ 0 := by
    intro hd_neg
    rw [h_signed_int]
    have hdmsb : dividend.msb = true := by
      by_contra h_f
      push_neg at h_f
      have h_msb_f : dividend.msb = false := by
        cases h' : dividend.msb; rfl; exact (h_f h').elim
      have := BitVec.toInt_nonneg_of_msb_false h_msb_f; omega
    simp [hdmsb]
  -- Sum equation: q.toInt * divisor.toInt + s.toInt = dividend.toInt.
  -- Lift h3 via toInt.
  have h_lift : ((q * divisor).toInt + s.toInt).bmod (2^64) = dividend.toInt := by
    have h_eq : (q * divisor + s).toInt = dividend.toInt := by rw [h3]
    rwa [BitVec.toInt_add] at h_eq
  rw [h_qdiv_toInt] at h_lift
  -- Bounds on s.toInt's magnitude.
  have h_s_abs : -(rem.toNat : Int) ≤ s.toInt ∧ s.toInt ≤ (rem.toNat : Int) := by
    rw [h_signed_int]
    by_cases hd : dividend.msb
    · simp [hd]
    · simp [hd]
  have h_rem_lt : (rem.toNat : Int) < (divisor.toInt.natAbs : Int) := by exact_mod_cast hbnd
  have h_div_natAbs : (divisor.toInt.natAbs : Int) ≤ 2^63 := by exact_mod_cast hdiv_natAbs_le
  -- dividend.toInt bounds.
  have hd_lo : -(2^63 : Int) ≤ dividend.toInt := by
    have := @BitVec.le_toInt 64 dividend; simpa using this
  have hd_hi : dividend.toInt < 2^63 := by
    have := @BitVec.toInt_lt 64 dividend; simpa using this
  -- Rule out wrap by bdiv decomposition + sign info.
  -- Key facts about bmod / bdiv applied to the sum.
  have h_bmod_range_lo : -(((2^64 : Nat) : Int) / 2) ≤
      (q.toInt * divisor.toInt + s.toInt).bmod (2^64) := Int.le_bmod (by norm_num)
  have h_bmod_range_hi :
      (q.toInt * divisor.toInt + s.toInt).bmod (2^64)
        < (((2^64 : Nat) : Int) + 1) / 2 := Int.bmod_lt (by norm_num)
  have h_bdiv_decomp :
      (q.toInt * divisor.toInt + s.toInt).bmod (2^64)
        = (q.toInt * divisor.toInt + s.toInt)
          - (2^64 : Nat) * (q.toInt * divisor.toInt + s.toInt).bdiv (2^64) :=
    Int.bmod_eq_self_sub_mul_bdiv _ _
  -- Normalize the 2^64 / 2 etc.
  have h64a : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
  have h64b : (((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int) := by decide
  rw [h64a] at h_bmod_range_lo
  rw [h64b] at h_bmod_range_hi
  rw [h_lift] at h_bdiv_decomp h_bmod_range_lo h_bmod_range_hi
  push_cast at h_bdiv_decomp
  -- Now show sum = dividend.toInt by case-split on dividend's sign and using h_s_sign_pos/neg.
  have h_sum_eq : q.toInt * divisor.toInt + s.toInt = dividend.toInt := by
    by_cases hd_nn : 0 ≤ dividend.toInt
    · have h_s_nn := h_s_sign_pos hd_nn
      -- s ≥ 0, q*d ≥ -2^63 → sum ≥ -2^63.
      -- bdiv ∈ {0, 1} from this.  We'll show bdiv = 0.
      omega
    · push_neg at hd_nn
      have h_s_np := h_s_sign_neg hd_nn
      -- s ≤ 0, q*d < 2^63 → sum < 2^63. bdiv ∈ {0, -1}.
      omega
  -- Apply int_uniqueness_step directly with h_sum_eq.
  obtain ⟨h_tdiv, h_tmod⟩ :=
    int_uniqueness_step (a := dividend.toInt) (b := divisor.toInt)
      (q := q.toInt) (r := s.toInt) hdivInt_ne
      h_sum_eq h_s_sign_pos h_s_sign_neg h_s_natAbs_lt
  -- Conclude q = sdiv.
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sdiv_of_ne_or_ne dividend divisor hne_pair]
    exact h_tdiv.symm
  · -- rem = bv_abs (BitVec.srem dividend divisor).
    apply BitVec.eq_of_toNat_eq
    rw [bv_abs_toNat_eq_natAbs, BitVec.toInt_srem, h_tmod]
    exact h_s_natAbs.symm

/-- **Uniqueness.** If some advice `(q, rem)` makes all four assertion
guards in `divProgram` pass, then `(q, rem)` is exactly the honest pair
`(sail_div_value …, bv_abs (sail_rem_value …))`.

This is the pure-math content behind soundness: the conjunction of the
four guards pins the advice down uniquely. Contrapositive form of
"bad advice ⇒ some guard fails". Proof plan — split on three cases:
`divisor = 0`, the signed-overflow pair `(INT_MIN, -1)`, and the
normal case (classical uniqueness of truncating quotient/remainder
with `|r| < |b|`, transported from `BitVec 64` to `Int` using guard 2
to rule out multiplicative overflow). -/
theorem advice_unique_of_guards
    (dividend divisor q rem adj : BitVec 64)
    (hadj : adj = change_divisor_value dividend divisor)
    (h1 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)))
    (h2 : mulhs q adj = (q * adj).sshiftRight 63)
    (h3 : q * adj +
            ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
          = dividend)
    (h4 : ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
            rem.toNat <
              ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) :
    q = sail_div_value dividend divisor false ∧
    rem = bv_abs (sail_rem_value dividend divisor false) := by
  by_cases h_zero : divisor = 0#64
  · -- divisor = 0 case
    -- q = -1 (from h1), adj = 0; h3 forces rem = bv_abs dividend.
    have hq_eq : q = -1 := by
      by_contra hne
      exact h1 ⟨h_zero, hne⟩
    have hadj_zero : adj = 0#64 := by
      rw [hadj]; unfold change_divisor_value; rw [h_zero]; simp
    refine ⟨?_, ?_⟩
    · -- q = sail_div_value dividend 0 false = -1
      rw [sail_div_value_of_zero dividend divisor h_zero, hq_eq]
    · -- rem = bv_abs(sail_rem) = bv_abs(dividend)
      rw [sail_rem_value_of_zero dividend divisor h_zero]
      apply rem_from_sign_fixup_eq
      -- h3 with q = -1, adj = 0: (-1) * 0 + signed_rem = d → signed_rem = d.
      rw [hq_eq, hadj_zero, BitVec.mul_zero, BitVec.zero_add] at h3
      exact h3
  · by_cases h_ovf : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1
    · -- Overflow case: adj = 1, rem = 0 (from h4), then q = INT_MIN (from h3).
      have hadj_eq : adj = 1#64 := by
        rw [hadj]; unfold change_divisor_value; rw [if_pos h_ovf]; rfl
      have habs_one : ((1#64 : BitVec 64) ^^^ (1#64 : BitVec 64).sshiftRight 63)
                        - (1#64 : BitVec 64).sshiftRight 63 = 1#64 := by decide
      have hrem_zero : rem = 0#64 := by
        rcases h4 with h0 | hlt
        · -- Left disjunct: |adj| = 0; with adj = 1 this is false.
          exfalso
          rw [hadj_eq, habs_one] at h0
          exact absurd h0 (by decide)
        · -- Right disjunct: rem.toNat < |adj|.toNat = 1, so rem = 0.
          rw [hadj_eq, habs_one] at hlt
          apply bv_eq_zero_of_toNat_lt_one
          have : ((1#64 : BitVec 64)).toNat = 1 := by decide
          rw [this] at hlt; exact hlt
      -- From h3 with adj = 1, rem = 0: q + 0 = dividend → q = dividend = INT_MIN.
      have hq_eq : q = (1 : BitVec 64) <<< 63 := by
        rw [hadj_eq, hrem_zero] at h3
        have hsigned_zero :
            ((0#64 : BitVec 64) ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63
              = 0#64 := by
          rw [BitVec.zero_xor, BitVec.sub_self]
        rw [hsigned_zero, BitVec.mul_one, BitVec.add_zero] at h3
        rw [h3, h_ovf.1]
      refine ⟨?_, ?_⟩
      · rw [sail_div_value_of_overflow dividend divisor h_ovf, hq_eq]
      · rw [sail_rem_value_of_normal dividend divisor h_zero, hrem_zero]
        -- bv_abs (BitVec.srem INT_MIN -1) = bv_abs 0 = 0
        symm
        apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_zero]
        -- bv_abs of (BitVec.srem INT_MIN -1) — need to compute
        obtain ⟨hd, hdv⟩ := h_ovf
        subst hd; subst hdv
        decide
    · -- Normal case: route through `advice_unique_normal`.
      have hadj_eq : adj = divisor := by
        rw [hadj]; unfold change_divisor_value; rw [if_neg h_ovf]
      have habs_div_pos : 0 < (bv_abs divisor).toNat := by
        rw [bv_abs_toNat_eq_natAbs]
        apply Int.natAbs_pos.mpr
        intro h; apply h_zero; apply BitVec.eq_of_toInt_eq
        rw [BitVec.toInt_zero]; exact h
      have hbnd_nat : rem.toNat < (bv_abs divisor).toNat := by
        rcases h4 with h0 | hlt
        · -- left disjunct |adj| = 0 contradicts |divisor| > 0 (after adj = divisor).
          exfalso
          rw [hadj_eq, ← bv_abs_eq_xor_sub_sign] at h0
          have : (bv_abs divisor).toNat = 0 := by rw [h0]; rfl
          omega
        · rw [hadj_eq, ← bv_abs_eq_xor_sub_sign] at hlt
          exact hlt
      have hbnd : rem.toNat < divisor.toInt.natAbs := by
        rw [← bv_abs_toNat_eq_natAbs]; exact hbnd_nat
      rw [hadj_eq] at h2 h3
      obtain ⟨hq, hrem⟩ :=
        advice_unique_normal dividend divisor q rem h_zero h_ovf h2 h3 hbnd
      refine ⟨?_, ?_⟩
      · rw [sail_div_value_of_normal dividend divisor h_zero h_ovf, hq]
      · rw [sail_rem_value_of_normal dividend divisor h_zero, hrem]

end
