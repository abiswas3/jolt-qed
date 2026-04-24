import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Pure BitVec/Int lemmas supporting the DIV proof

Mathematical content that underpins the assertion-guard arguments in
`jolt_div`'s completeness proof. Kept separate from `Div.lean` so that
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
  holds under honest advice. Consumed by `jolt_div_concrete` in
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
-- Each of the four lemmas below closes one of the asserts in `jolt_div`,
-- showing that the guard condition follows purely from the fact that
-- the oracle produced the advice Sail would produce. No trust is placed
-- in the oracle beyond "it returned `sail_div_value` / `sail_rem_value`".
--
-- The guards, in order of appearance in the Jolt sequence:
--   1. `VirtualAssertValidDiv0`        — step 3
--   2. `VirtualAssertEQ v3 v5`         — step 8  (overflow check)
--   3. `VirtualAssertEQ v4 rs1`        — step 13 (quotient·divisor + r = dividend)
--   4. `VirtualAssertValidUnsignedRemainder` — step 17 (|r| < |adj|)

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
  sorry

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
  sorry

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
      (rem ^^^ dividend.sshiftRight 63 - dividend.sshiftRight 63)
      = dividend := by
  sorry

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
    rem.toNat < (adj ^^^ adj.sshiftRight 63 - adj.sshiftRight 63).toNat := by
  sorry

-- ----------------------------------------------------------------------------
-- Uniqueness of advice — soundness core
-- ----------------------------------------------------------------------------

/-- **Uniqueness.** If some advice `(q, rem)` makes all four assertion
guards in `jolt_div` pass, then `(q, rem)` is exactly the honest pair
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
            (rem ^^^ dividend.sshiftRight 63 - dividend.sshiftRight 63)
          = dividend)
    (h4 : rem.toNat <
            (adj ^^^ adj.sshiftRight 63 - adj.sshiftRight 63).toNat) :
    q = sail_div_value dividend divisor false ∧
    rem = bv_abs (sail_rem_value dividend divisor false) := by
  sorry

end
