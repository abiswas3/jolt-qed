import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
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
same file — and so `Div.lean` doesn't need the full `import Mathlib`.
-/

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

end
