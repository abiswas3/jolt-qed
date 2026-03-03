import Mathlib.Tactic
import Mathlib.Data.BitVec
import JoltBytecode.BytecodeExpansions.Common.Riscv

set_option maxHeartbeats 3200000

/-!
# No-overflow lemma for 64-bit signed multiplication

When MULH(a,b) = sign-extend(MUL(a,b)), the true signed product fits in
64 bits: MUL(a,b).toInt = a.toInt * b.toInt.
-/

/-- `Int.bmod x m = x` when `x` lies in the balanced range `[-(m/2), (m+1)/2)`. -/
private lemma Int.bmod_eq_of_range {x : Int} {m : Nat} (hm : 0 < m)
    (h_lo : -((m : Int) / 2) ≤ x) (h_hi : x < ((m : Int) + 1) / 2) :
    Int.bmod x m = x := by
  set b := Int.bmod x m
  have hb_lo : -((m : Int) / 2) ≤ b := Int.le_bmod hm
  have hb_hi : b < ((m : Int) + 1) / 2 := Int.bmod_lt hm
  have hb_dvd : (m : Int) ∣ b - x := Int.dvd_bmod_sub_self
  obtain ⟨k, hk⟩ := hb_dvd
  have h_diff_lo : -(m : Int) < b - x := by omega
  have h_diff_hi : b - x < (m : Int) := by omega
  have hm_nn : (0 : Int) ≤ (m : Nat) := Int.ofNat_nonneg m
  have hk0 : k = 0 := by
    by_contra hn
    cases Int.lt_or_gt_of_ne hn with
    | inl hk_neg =>
      have : (m : Int) * k ≤ (m : Int) * (-1) :=
        Int.mul_le_mul_of_nonneg_left (by omega : k ≤ -1) hm_nn
      linarith
    | inr hk_pos =>
      have : (m : Int) * 1 ≤ (m : Int) * k :=
        Int.mul_le_mul_of_nonneg_left (by omega : 1 ≤ k) hm_nn
      linarith
  rw [hk0, mul_zero] at hk; linarith

/-- The high part P / 2^64 of the signed product of two 64-bit bitvectors
    is in balanced range [-2^63, 2^63). -/
private lemma high_part_in_range_64 (a b : BitVec 64) :
    -(2 ^ 63 : Int) ≤ (a.toInt * b.toInt) / (2 ^ 64 : Int) ∧
    (a.toInt * b.toInt) / (2 ^ 64 : Int) < 2 ^ 63 := by
  set P := a.toInt * b.toInt
  have ha_lo : -(2 ^ 63 : Int) ≤ a.toInt := by
    rw [BitVec.toInt_eq_toNat_bmod]
    have := Int.le_bmod (x := (a.toNat : Int)) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  have ha_hi : a.toInt < 2 ^ 63 := by
    rw [BitVec.toInt_eq_toNat_bmod]
    have := Int.bmod_lt (x := (a.toNat : Int)) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  have hb_lo : -(2 ^ 63 : Int) ≤ b.toInt := by
    rw [BitVec.toInt_eq_toNat_bmod]
    have := Int.le_bmod (x := (b.toNat : Int)) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  have hb_hi : b.toInt < 2 ^ 63 := by
    rw [BitVec.toInt_eq_toNat_bmod]
    have := Int.bmod_lt (x := (b.toNat : Int)) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  set lo := -(2 ^ 63 : Int)
  set hi := (2 ^ 63 : Int)
  set M := (2 ^ 64 : Int)
  have hM_pos : (0 : Int) < M := by omega
  have hM_eq : M = hi + hi := by omega
  have hhi_pos : (0 : Int) < hi := by omega
  constructor
  · -- Lower bound: lo ≤ P / M, equivalently lo * M ≤ P
    rw [Int.le_ediv_iff_mul_le hM_pos]
    by_cases hb_sign : 0 ≤ b.toInt
    · -- a ≥ lo, b ≥ 0: P ≥ lo * b ≥ lo * M
      have h₁ : lo * b.toInt ≤ P := Int.mul_le_mul_of_nonneg_right ha_lo hb_sign
      have h₂ : lo * M ≤ lo * b.toInt := Int.mul_le_mul_of_nonpos_left (by omega) (by omega)
      linarith
    · -- a ≤ hi-1, b < 0: lo*M ≤ (hi-1)*lo ≤ (hi-1)*b ≤ P
      push_neg at hb_sign
      have ha_ub : a.toInt ≤ hi - 1 := Int.le_sub_one_of_lt ha_hi
      have h₁ : (hi - 1) * b.toInt ≤ P := Int.mul_le_mul_of_nonpos_right ha_ub (by omega)
      have h_mid_nn : 0 ≤ (hi - 1) * lo - lo * M := by
        have h_calc : (hi - 1) * lo - lo * (hi + hi) = (-lo) * (hi + 1) := by ring
        have h_sub : lo * M = lo * (hi + hi) := by simp only [hM_eq]
        rw [h_sub, h_calc]
        exact mul_nonneg (by omega : (0 : Int) ≤ -lo) (by omega : (0 : Int) ≤ hi + 1)
      have h_step : (hi - 1) * lo ≤ (hi - 1) * b.toInt :=
        Int.mul_le_mul_of_nonneg_left hb_lo (by omega : 0 ≤ hi - 1)
      linarith
  · -- Upper bound: P / M < hi, equivalently P < hi * M
    rw [Int.ediv_lt_iff_lt_mul hM_pos]
    by_cases ha_sign : 0 ≤ a.toInt
    · by_cases hb_sign : 0 ≤ b.toInt
      · -- Both nonneg: P ≤ (hi-1)^2 < hi*M
        have ha_ub := Int.le_sub_one_of_lt ha_hi
        have hb_ub := Int.le_sub_one_of_lt hb_hi
        have h₁ : P ≤ (hi - 1) * (hi - 1) :=
          Int.mul_le_mul ha_ub hb_ub hb_sign (by omega : 0 ≤ hi - 1)
        -- hi*M - (hi-1)^2 = hi^2 + 2*hi - 1 > 0
        have h_gap_nn : 0 < hi * M - (hi - 1) * (hi - 1) := by
          have _h_ring : hi * (hi + hi) - (hi - 1) * (hi - 1) = hi * hi + 2 * hi - 1 := by ring
          have h_unfold : hi * M = hi * (hi + hi) := by simp only [hM_eq]
          have h_sq_pos : 0 < hi * hi := Int.mul_pos hhi_pos hhi_pos
          linarith
        linarith
      · -- a ≥ 0, b < 0: P ≤ 0 < hi*M
        push_neg at hb_sign
        have : P ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos ha_sign (by omega)
        have : 0 < hi * M := Int.mul_pos hhi_pos hM_pos
        linarith
    · by_cases hb_sign : 0 ≤ b.toInt
      · -- a < 0, b ≥ 0: P ≤ 0 < hi*M
        push_neg at ha_sign
        have : P ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hb_sign
        have : 0 < hi * M := Int.mul_pos hhi_pos hM_pos
        linarith
      · -- Both negative: P = (-a)*(-b) ≤ hi*hi < hi*M
        push_neg at ha_sign hb_sign
        -- P = a*b, and -a ≤ hi, -b ≤ hi, so P ≤ hi^2
        have h_prod : P ≤ hi * hi := by
          have ha_neg : -(a.toInt) ≤ hi := by omega
          have hb_neg : -(b.toInt) ≤ hi := by omega
          -- (hi + a)(hi + b) ≥ 0 expands to hi^2 + hi*(a+b) + a*b ≥ 0
          -- i.e., P ≥ -(hi^2 + hi*(a+b)), but we need P ≤ hi^2.
          -- Actually: P = (-a)*(-b) ≤ hi * hi directly
          have := Int.mul_le_mul ha_neg hb_neg (by omega : 0 ≤ -(b.toInt)) (by omega : 0 ≤ hi)
          linarith [show P = -(a.toInt) * -(b.toInt) from by ring]
        -- hi^2 < hi*M because M > hi (M = 2*hi)
        have : hi * hi < hi * M :=
          Int.mul_lt_mul_of_pos_left (by omega : hi < M) hhi_pos
        linarith

/-- No-overflow helper: when MULH(a,b) = sign-extend(MUL(a,b)), the true
    signed product fits in 64 bits: MUL(a,b).toInt = a.toInt * b.toInt. -/
lemma no_overflow_implies_mul_toInt_eq (a b : BitVec 64)
    (h : Riscv.mulh a b = (Riscv.mul a b).sshiftRight 63) :
    (Riscv.mul a b).toInt = a.toInt * b.toInt := by
  set P := a.toInt * b.toInt with hP_def
  unfold Riscv.mul
  rw [BitVec.toInt_mul, ← hP_def]
  -- Extract information from hypothesis
  unfold Riscv.mulh Riscv.mul at h
  have h_eq := congrArg BitVec.toInt h
  simp only [BitVec.toInt_ofInt, BitVec.sshiftRight_eq, BitVec.toInt_mul] at h_eq
  rw [← hP_def] at h_eq
  -- The high part is in range, so its bmod is the identity
  have h_hr := high_part_in_range_64 a b
  simp only [← hP_def] at h_hr
  have h_high_bmod : Int.bmod (P / (2 ^ 64 : Int)) (2 ^ 64 : Nat) = P / (2 ^ 64 : Int) :=
    Int.bmod_eq_of_range (by positivity)
      (by norm_num; exact h_hr.1) (by norm_num; exact h_hr.2)
  simp only [h_high_bmod] at h_eq
  -- Analyze the low part L = P.bmod(2^64)
  set L := P.bmod (2 ^ 64 : Nat) with hL_def
  have hL_lo : -(2 ^ 63 : Int) ≤ L := by
    have := Int.le_bmod (x := P) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  have hL_hi : L < 2 ^ 63 := by
    have := Int.bmod_lt (x := P) (m := (2 ^ 64 : Nat)) (by positivity)
    norm_num at this; exact this
  -- Rewrite shift to division in h_eq
  simp only [show L >>> (63 : Nat) = L / (2 ^ 63 : Int) from Int.shiftRight_eq_div_pow L 63] at h_eq
  -- Case split on sign of L
  by_cases hL_sign : 0 ≤ L
  · -- L ≥ 0: L / 2^63 = 0
    have h_div_zero : L / (2 ^ 63 : Int) = 0 := Int.ediv_eq_zero_of_lt hL_sign (by omega)
    simp only [h_div_zero] at h_eq
    simp [Int.bmod_zero] at h_eq
    have h_emod := (Int.ediv_add_emod P (2 ^ 64 : Int)).symm
    simp only [h_eq, mul_zero, zero_add] at h_emod
    simp only [hL_def, Int.bmod_def] at hL_sign
    split_ifs at hL_sign with h_small
    · norm_num at h_small
      exact Int.bmod_eq_of_range (by positivity) (by norm_num; omega) (by norm_num; omega)
    · exfalso; norm_num at h_small; omega
  · -- L < 0: L / 2^63 = -1
    push_neg at hL_sign
    have h_rem_nn : 0 ≤ L + (2 : Int) ^ 63 := by omega
    have _h_rem_lt : L + (2 : Int) ^ 63 < (2 : Int) ^ 63 := by omega
    have h_decomp : L = (L + (2 : Int) ^ 63) + (2 : Int) ^ 63 * (-1) := by ring
    have h_div_neg1 : L / (2 : Int) ^ 63 = -1 := by
      rw [h_decomp, Int.add_mul_ediv_left _ _ (show (2 : Int) ^ 63 ≠ 0 from by positivity),
          Int.ediv_eq_zero_of_lt h_rem_nn (by linarith)]
      ring
    simp only [h_div_neg1] at h_eq
    have h_neg1_bmod : Int.bmod (-1 : Int) (2 ^ 64 : Nat) = -1 :=
      Int.bmod_eq_of_range (by positivity) (by norm_num) (by norm_num)
    simp only [h_neg1_bmod] at h_eq
    -- h_eq : P / 2^64 = -1
    have h_emod := (Int.ediv_add_emod P (2 ^ 64 : Int)).symm
    simp only [h_eq] at h_emod
    have _h_emod_nn := Int.emod_nonneg P (show (2 ^ 64 : Int) ≠ 0 by positivity)
    simp only [hL_def, Int.bmod_def] at hL_sign
    split_ifs at hL_sign with h_small
    · norm_num at h_small; omega
    · norm_num at h_small
      exact Int.bmod_eq_of_range (by positivity) (by norm_num; omega) (by norm_num; omega)
