import JoltBytecode.BytecodeExpansions.Common.Virtual

/-!
# Shared simp lemmas

Reusable lemmas for `ctz` and bitwise arithmetic, used across multiple
shift-instruction proofs (SRAW, SRAIW, SRLIW, SRLI, SRAI, etc.).
-/

-- ============================================================================
-- ctz lemmas
-- ============================================================================

-- An odd number has zero trailing zeros.
lemma ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  have hne : n ≠ 0 := by omega
  unfold ctz; rw [if_neg hne, if_pos h]

-- Doubling a positive number adds one trailing zero.
lemma ctz_of_double {n : Nat} (hn : 0 < n) : ctz (2 * n) = 1 + ctz n := by
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : ¬(2 * n % 2 = 1) := by omega
  have h3 : (2 * n) / 2 = n := by omega
  conv_lhs => unfold ctz
  rw [if_neg h1, if_neg h2, h3]

-- Multiplying by 2^k adds k trailing zeros.
lemma ctz_mul_pow2 (k : Nat) {m : Nat} (hm : 0 < m) :
    ctz (2 ^ k * m) = k + ctz m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_rw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [h_rw, ctz_of_double (by positivity), ih]
    omega

-- 2^k - 1 is odd for k > 0.
lemma pow2_sub_one_odd {k : Nat} (hk : 0 < k) : (2 ^ k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    rw [pow_succ, mul_comm]
    have : 0 < 2 ^ n := by positivity
    omega

-- ============================================================================
-- Shift-as-multiply
-- ============================================================================

-- Left-shifting by s equals multiplying by 2^s (any width).
@[simp]
lemma shiftLeft_eq_mul_pow2 (x : BitVec 64) (s : Nat) :
    x <<< s = x * BitVec.ofNat 64 (2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

-- ============================================================================
-- Arithmetic right shift via sign-extend + logical shift
-- ============================================================================

-- Arithmetic right shift of a 32-bit value equals: sign-extend to 64,
-- logical right shift, truncate back to 32.
lemma sshiftRight_eq_signExtend_ushr_trunc (x : BitVec 32) (s : Nat) (hs : s < 32) :
    x.sshiftRight s = (x.signExtend 64 >>> s).setWidth 32 := by
  ext i
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  simp [i.isLt, show ¬(32 ≤ (↑i : Nat)) from by omega,
        show s + (↑i : Nat) < 64 from by omega]
