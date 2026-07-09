import JoltBytecode.JoltISA.Values

/-!
# Proof-theory lemmas about `JoltISA/Values` helpers

These theorems characterise the helper functions in `JoltBytecode/JoltISA/Values.lean`
(the pure value layer of the Jolt ISA).  The definitions stay in the ISA layer;
the proof-side facts about them live here, with the rest of the instruction
equivalence machinery.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

-- ============================================================================
-- ctz / pow2 number-theory lemmas (moved from JoltISA/Values/Shift.lean)
-- ============================================================================

@[simp] lemma ctz_pow2 (n : Nat) : ctz (2 ^ n) = n := by
  induction n with
  | zero => unfold ctz; simp
  | succ k ih =>
    unfold ctz
    rw [if_neg (show 2 ^ (k + 1) ≠ 0 from Nat.pos_iff_ne_zero.mp (by positivity))]
    rw [if_neg (show ¬(2 ^ (k + 1) % 2 = 1) from by rw [pow_succ]; omega)]
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k from by rw [pow_succ]; omega]
    rw [ih]; omega

lemma ctz_of_odd {n : Nat} (h : n % 2 = 1) : ctz n = 0 := by
  have hne : n ≠ 0 := by omega
  unfold ctz; rw [if_neg hne, if_pos h]

lemma ctz_of_double {n : Nat} (hn : 0 < n) : ctz (2 * n) = 1 + ctz n := by
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : ¬(2 * n % 2 = 1) := by omega
  have h3 : (2 * n) / 2 = n := by omega
  conv_lhs => unfold ctz
  rw [if_neg h1, if_neg h2, h3]

lemma ctz_mul_pow2 (k : Nat) {m : Nat} (hm : 0 < m) :
    ctz (2 ^ k * m) = k + ctz m := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_rw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [h_rw, ctz_of_double (by positivity), ih]
    omega

lemma pow2_sub_one_odd {k : Nat} (hk : 0 < k) : (2 ^ k - 1) % 2 = 1 := by
  cases k with
  | zero => omega
  | succ n =>
    rw [pow_succ, mul_comm]
    have : 0 < 2 ^ n := by positivity
    omega

-- ============================================================================
-- Shared BitVec shift lemmas (moved from JoltISA/Values/Shift.lean)
-- ============================================================================

@[simp]
lemma shiftLeft_eq_mul_pow2 (x : BitVec 64) (s : Nat) :
    x <<< s = x * BitVec.ofNat 64 (2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

lemma sshiftRight_eq_signExtend_ushr_trunc (x : BitVec 32) (s : Nat) (hs : s < 32) :
    x.sshiftRight s = (x.signExtend 64 >>> s).setWidth 32 := by
  ext i hi
  simp only [BitVec.getElem_sshiftRight, BitVec.getElem_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  simp only [show s + i < 64 from by omega, decide_true, Bool.true_and]
  split
  · rename_i hsi; simp [BitVec.getLsbD_eq_getElem, hsi]
  · rfl

-- ============================================================================
-- Lemmas about JoltISA/Values defs
-- ============================================================================

/-- If a 64-bit word is below `2^63`, `VirtualMovsign` returns zero. -/
theorem jolt_movsign_value_eq_zero_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    jolt_movsign_value x = 0 := by
  unfold jolt_movsign_value
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false_iff_not.mpr (by omega)
  rw [hmsb]
  rfl

/-- If a 64-bit word is at least `2^63`, `VirtualMovsign` returns all ones. -/
theorem jolt_movsign_value_eq_neg_one_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    jolt_movsign_value x = (-1 : BitVec 64) := by
  unfold jolt_movsign_value
  have hmsb : x.msb = true := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_true_eq.mpr (by omega)
  rw [hmsb]
  rfl

/-- Extracting the low 64 bits of a 128-bit truncated integer is the same as
viewing that integer as a 64-bit bitvector. -/
private theorem extract_low64_to_bits_truncate_eq_ofInt (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 63 0 : BitVec 64) =
      BitVec.ofInt 64 p := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', to_bits_truncate,
        Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  have hnonneg : 0 ≤ p % (680564733841876926926749214863536422912 : Int) := by
    exact Int.emod_nonneg p (by norm_num)
  have hcast : (((p % (680564733841876926926749214863536422912 : Int)).toNat : Nat) : Int) =
      p % (680564733841876926926749214863536422912 : Int) := by
    exact Int.toNat_of_nonneg hnonneg
  have hnat_mod :
      (((p % (680564733841876926926749214863536422912 : Int)).toNat %
        18446744073709551616 : Nat) : Int) =
      ((p % (680564733841876926926749214863536422912 : Int)).toNat : Int) %
        (18446744073709551616 : Int) := by
    exact Int.natCast_emod
      ((p % (680564733841876926926749214863536422912 : Int)).toNat)
      18446744073709551616
  have h_dvd : (18446744073709551616 : Int) ∣
      (680564733841876926926749214863536422912 : Int) := by
    norm_num
  have h_int :
      (((p % (680564733841876926926749214863536422912 : Int)).toNat %
        18446744073709551616 : Nat) : Int) =
      ((p % (18446744073709551616 : Int)).toNat : Nat) := by
    rw [hnat_mod, hcast, Int.emod_emod_of_dvd p h_dvd]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg p (by norm_num))).symm
  exact_mod_cast h_int

/-- Signed interpretation of the operands does not affect the low 64 bits of a
64-bit product. -/
private theorem BitVec.ofInt_mul_toInt_eq_mul (x y : BitVec 64) :
    BitVec.ofInt 64 (x.toInt * y.toInt) = x * y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]
  have hx : x.toInt % (18446744073709551616 : Int) =
      (x.toNat : Int) % (18446744073709551616 : Int) := by
    rw [BitVec.toInt]
    split
    · rfl
    · omega
  have hy : y.toInt % (18446744073709551616 : Int) =
      (y.toNat : Int) % (18446744073709551616 : Int) := by
    rw [BitVec.toInt]
    split
    · rfl
    · omega
  have hprod : (x.toInt * y.toInt) % (18446744073709551616 : Int) =
      ((x.toNat : Int) * (y.toNat : Int)) % (18446744073709551616 : Int) := by
    calc
      (x.toInt * y.toInt) % (18446744073709551616 : Int)
          = ((x.toInt % (18446744073709551616 : Int)) *
              (y.toInt % (18446744073709551616 : Int))) %
              (18446744073709551616 : Int) := by
            rw [Int.mul_emod]
      _ = (((x.toNat : Int) % (18446744073709551616 : Int)) *
              ((y.toNat : Int) % (18446744073709551616 : Int))) %
              (18446744073709551616 : Int) := by
            rw [hx, hy]
      _ = ((x.toNat : Int) * (y.toNat : Int)) % (18446744073709551616 : Int) := by
            rw [← Int.mul_emod]
  have hnat_mod :
      (((x.toNat * y.toNat : Nat) % 18446744073709551616 : Nat) : Int) =
        ((x.toNat : Int) * (y.toNat : Int)) % (18446744073709551616 : Int) := by
    rw [← Nat.cast_mul]
    exact Int.natCast_emod (x.toNat * y.toNat) 18446744073709551616
  rw [hprod]
  exact congrArg Int.toNat hnat_mod.symm

/-- Sail's signed/signed low-half multiply agrees with Jolt's native `MUL`
value. -/
theorem sail_mul_value_eq_jolt_mul_value (x y : BitVec 64) :
    mult_to_bits_half (l := LeanRV64D.Functions.xlen)
      Signedness.Signed Signedness.Signed x y VectorHalf.Low =
    x * y := by
  unfold mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (x.toInt * y.toInt)) 63 0) =
    x * y
  rw [extract_low64_to_bits_truncate_eq_ofInt]
  simp only [BitVec.setWidth_eq]
  exact BitVec.ofInt_mul_toInt_eq_mul x y

/-- Sail's unsigned/unsigned high-half multiply agrees with Jolt's `MULHU`
value helper. -/
theorem sail_mulhu_value_eq_jolt_mulhu_value (x y : BitVec 64) :
    mult_to_bits_half (l := LeanRV64D.Functions.xlen)
      Signedness.Unsigned Signedness.Unsigned x y VectorHalf.High =
    jolt_mulhu_value x y := by
  have h_extract :
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) ((x.toNat : Int) * (y.toNat : Int)))
        127 64 : BitVec 64) =
        BitVec.ofInt 64 (((x.toNat : Int) * (y.toNat : Int)) / 2^64) := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      to_bits_truncate, Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
    omega
  unfold jolt_mulhu_value mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) ((x.toNat : Int) * (y.toNat : Int)))
        127 64) =
      BitVec.ofNat 64 (x.toNat * y.toNat / 2^64)
  rw [h_extract]
  have h_div :
      ((x.toNat : Int) * (y.toNat : Int) / (2^64 : Int)) =
        ((x.toNat * y.toNat / 2^64 : Nat) : Int) := by
    rw [← Nat.cast_mul]
    exact (Int.natCast_ediv (x.toNat * y.toNat) (2^64)).symm
  have h_div_num :
      ((x.toNat : Int) * (y.toNat : Int) / (18446744073709551616 : Int)) =
        ((x.toNat * y.toNat / 18446744073709551616 : Nat) : Int) := by
    norm_num at h_div ⊢
  apply BitVec.eq_of_toNat_eq
  simp
  have h_mod := congrArg
    (fun z : Int => (z % (18446744073709551616 : Int)).toNat)
    h_div_num
  have h_mod' :
      ((↑x.toNat * ↑y.toNat / (18446744073709551616 : Int)) %
          (18446744073709551616 : Int)).toNat =
        (((x.toNat * y.toNat / 18446744073709551616 : Nat) : Int) %
          (18446744073709551616 : Int)).toNat := by
    simpa only using h_mod
  have h_nat_mod :
      (((x.toNat * y.toNat / 18446744073709551616 : Nat) : Int) %
          (18446744073709551616 : Int)).toNat =
        x.toNat * y.toNat / 18446744073709551616 %
          18446744073709551616 := by
    exact congrArg Int.toNat
      (Int.natCast_emod
        (x.toNat * y.toNat / 18446744073709551616)
        18446744073709551616).symm
  exact h_mod'.trans h_nat_mod

/-- The natural-number bitmask encoded by `VirtualShiftRightBitmask` fits in
64 bits.  This justifies reading the produced `BitVec 64` back as a `Nat`
without changing the trailing-zero structure consumed by `VirtualSRL` and
`VirtualSRA`. -/
private theorem jolt_virtual_shift_right_bitmask_nat_lt (x : BitVec 64) :
    (let shift := (x.setWidth 6).toNat
     let ones := (1 <<< (64 - shift)) - 1
     ones <<< shift) < 2 ^ 64 := by
  simp only [Nat.shiftLeft_eq]
  set shift := (x.setWidth 6).toNat
  have hshift_lt : shift < 64 := by
    have := (x.setWidth 6).isLt
    norm_num at this
    exact this
  have hdiff_pos : 0 < 64 - shift := by omega
  have hones_lt : 2 ^ (64 - shift) - 1 < 2 ^ (64 - shift) := by
    have hpow_pos : 0 < 2 ^ (64 - shift) := by positivity
    omega
  have hmul_lt :
      (2 ^ (64 - shift) - 1) * 2 ^ shift <
        2 ^ (64 - shift) * 2 ^ shift :=
    Nat.mul_lt_mul_of_pos_right hones_lt (by positivity)
  have hpow : 2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  simpa [hpow] using hmul_lt

/-- Reading back the `VirtualShiftRightBitmask` result as a natural number
recovers the same encoded bitmask used in the Rust expansion. -/
theorem jolt_virtual_shift_right_bitmask_value_toNat (x : BitVec 64) :
    (jolt_virtual_shift_right_bitmask_value x).toNat =
      (let shift := (x.setWidth 6).toNat
       let ones := (1 <<< (64 - shift)) - 1
       ones <<< shift) := by
  unfold jolt_virtual_shift_right_bitmask_value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact jolt_virtual_shift_right_bitmask_nat_lt x

/-- The essential contract of `VirtualShiftRightBitmask`: the word it writes
has exactly `x[5:0]` trailing zeroes.  `VirtualSRL` and `VirtualSRA` consume
only this `ctz` value, so this lemma is the reusable bridge from the virtual
instruction to ordinary Sail shifts. -/
theorem ctz_jolt_virtual_shift_right_bitmask_value (x : BitVec 64) :
    ctz (jolt_virtual_shift_right_bitmask_value x).toNat =
      (x.setWidth 6).toNat := by
  rw [jolt_virtual_shift_right_bitmask_value_toNat]
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (x.setWidth 6).toNat
  have h_lt : shift < 64 := by
    have := (x.setWidth 6).isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos,
    ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

/-- `SLTU` returns one when the unsigned comparison is true. -/
theorem jolt_sltu_value_eq_one_of_lt (x y : BitVec 64)
    (h : x.toNat < y.toNat) :
    jolt_sltu_value x y = 1 := by
  unfold jolt_sltu_value zopz0zI_u BitVec.toNatInt bool_to_bit
    bool_bit_forwards zero_extend
  simp [h]
  decide

/-- `SLTU` returns zero when the unsigned comparison is false. -/
theorem jolt_sltu_value_eq_zero_of_not_lt (x y : BitVec 64)
    (h : ¬ x.toNat < y.toNat) :
    jolt_sltu_value x y = 0 := by
  unfold jolt_sltu_value zopz0zI_u BitVec.toNatInt bool_to_bit
    bool_bit_forwards zero_extend
  simp [h]
  decide

/-- The natural-number value of `jolt_sltu_value` is the expected Boolean flag,
viewed as `0` or `1`. -/
theorem jolt_sltu_value_toNat (x y : BitVec 64) :
    (jolt_sltu_value x y).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x.toNat < y.toNat
  · rw [jolt_sltu_value_eq_one_of_lt x y h]
    simp [h]
  · rw [jolt_sltu_value_eq_zero_of_not_lt x y h]
    simp [h]

end
