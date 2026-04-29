import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `jolt_divw` (advice-verified DIVW)

The DIVW counterpart of `Div_math.lean`. Provides:

* The five **honest-advice guard lemmas** — `hguard_div0_of_honest_w`,
  `hguard_q_fits_of_honest_w`, `hguard_rem_nonneg_of_honest_w`,
  `hguard_quotient_product_of_honest_w`, `hguard_rem_bound_of_honest_w`
  — showing that each assertion's guard is satisfied when the oracle
  returns the honest values `(sail_divw_value, bv_abs sail_remw_value)`.
* A small Sail-side utility `rX_bits_x0_eq_zero` (reading register
  zero always yields `0#64`) used to discharge the `hx0` argument of
  `Divw.phase_rem_nonneg_run`.

Note: where DIV uses `shamt = 63` (sign bit of a 64-bit value), DIVW
uses `shamt = 31` (sign bit of a 32-bit value, sign-extended). The
moduli throughout shift accordingly.
-/

-- ----------------------------------------------------------------------------
-- Sail-side honest advice values
-- ----------------------------------------------------------------------------

/-- The pure 64-bit value `execute_DIVW rs2 rs1 rd is_unsigned` writes to
`rd`, given the values read from `rs1` and `rs2`. Verbatim copy of the
`execute_DIVW` body (minus the monadic read/write/return wrapper),
transcribed from `LeanRV64D/InstsEnd.lean:71082`. -/
def sail_divw_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_low) else (BitVec.toInt rs1_low)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_low) else (BitVec.toInt rs2_low)
  let quotient :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31)) else quotient
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-- 32-bit signed remainder corresponding to `sail_divw_value`. The
remainder advice supplied to `jolt_divw` is `bv_abs (sail_remw_value …)`,
matching the `quotient × divisor + remainder = dividend` identity at
32-bit width (sign-extended). -/
def sail_remw_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_low) else (BitVec.toInt rs1_low)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_low) else (BitVec.toInt rs2_low)
  let remainder :=
    if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)

-- The honest values, used by every guard lemma below.
section HonestValues
variable (dividend divisor : BitVec 64)

/-- Honest oracle quotient — the same value `execute_DIVW` writes to `rd`. -/
abbrev q_w  := sail_divw_value dividend divisor false
/-- Honest oracle `|remainder|`. -/
abbrev rem_w := bv_abs (sail_remw_value dividend divisor false)
/-- Sign-extended low 32 bits of `rs1` (the value carried in virtual `v6`). -/
abbrev sext_dividend_w :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
/-- Sign-extended low 32 bits of `rs2` (the value carried in virtual `v5`). -/
abbrev sext_divisor_w :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
/-- Adjusted divisor after the `(i32::MIN, -1)` overflow fix-up. -/
abbrev adj_w :=
  change_divisor_w_value (sext_dividend_w dividend) (sext_divisor_w divisor)

end HonestValues

-- ----------------------------------------------------------------------------
-- Sail-side utility: reading register x0 yields zero
-- ----------------------------------------------------------------------------

/-- Reading register zero from any Sail state returns `0#64` without
side effects. RV64 hardwires `x0 ≡ 0` per the ISA spec; the Sail
transpilation reflects this in `rX (Regno 0) = pure zero_reg`. Used
to discharge `Divw.phase_rem_nonneg_run`'s `hx0` argument. -/
theorem rX_bits_x0_eq_zero (s : SailState) :
    rX_bits (regidx.Regidx 0) s = .ok 0#64 s := by
  unfold rX_bits rX regval_from_reg zero_reg zeros
  simp [Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

-- ----------------------------------------------------------------------------
-- Round-trip helpers for `to_bits_truncate ∘ BitVec.toInt` (32-bit)
-- ----------------------------------------------------------------------------

private theorem mod33_toNat_mod32 (x : Int) :
    (x % 8589934592).toNat % 4294967296
      = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x
        = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32 x

-- ----------------------------------------------------------------------------
-- Sign-extension helpers for 32-bit values in 64-bit BitVec
-- ----------------------------------------------------------------------------

-- Extracting the low 32 bits of a 64-bit sign-extension of a 32-bit value
-- gives back the original 32-bit value.
private lemma extractLsb_signExtend_32_64 (x : BitVec 32) :
    (x.signExtend 64).extractLsb 31 0 = x := by
  bv_decide

/-- For a sign-extended 32-bit value, `sshiftRight 31 = sshiftRight 63`.
Both produce the sign-broadcast (all-zeros or all-ones). -/
private lemma sshiftRight31_eq_63_of_sext32 (x : BitVec 32) :
    (x.signExtend 64 : BitVec 64).sshiftRight 31 =
    (x.signExtend 64 : BitVec 64).sshiftRight 63 := by
  bv_decide

/-- `bv_abs` of a sign-extended 32-bit value, arithmetic-shifted right by 32,
is zero — i.e., the absolute value fits in u32. -/
private lemma bv_abs_sext32_sshiftRight32 (x : BitVec 32) :
    (bv_abs (sign_extend (m := 64) x)).sshiftRight 32 = 0#64 := by
  unfold bv_abs sign_extend Sail.BitVec.signExtend
  split_ifs <;> bv_decide

private lemma eq_zero_of_signExtend32_eq_zero (x : BitVec 32)
    (h : sign_extend (m := 64) x = 0#64) : x = 0#32 := by
  revert h
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma sshiftRight63_signExtend_eq_of_msb_eq (x y : BitVec 32)
    (h : x.msb = y.msb) :
    (sign_extend (m := 64) x).sshiftRight 63 =
    (sign_extend (m := 64) y).sshiftRight 63 := by
  revert h
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma toInt_signExtend32_64 (x : BitVec 32) :
    (sign_extend (m := 64) x).toInt = x.toInt := by
  unfold sign_extend Sail.BitVec.signExtend
  rw [BitVec.toInt_signExtend]
  have hlo : -(2^31 : Int) ≤ x.toInt := by
    have := @BitVec.le_toInt 32 x
    simpa using this
  have hhi : x.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 x
    simpa using this
  apply Int.bmod_eq_of_le
  · show -(((2^32 : Nat) : Int) / 2) ≤ x.toInt
    have h : (((2^32 : Nat) : Int) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hlo
  · show x.toInt < ((((2^32 : Nat) : Int) + 1) / 2)
    have h : ((((2^32 : Nat) : Int) + 1) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hhi

private lemma xor_sub_sign31_sext32_eq_bv_abs (x : BitVec 32) :
    ((sign_extend (m := 64) x ^^^ (sign_extend (m := 64) x).sshiftRight 31) -
      (sign_extend (m := 64) x).sshiftRight 31) =
    bv_abs (sign_extend (m := 64) x) := by
  unfold sign_extend Sail.BitVec.signExtend
  rw [sshiftRight31_eq_63_of_sext32]
  exact (bv_abs_eq_xor_sub_sign (x.signExtend 64)).symm

private lemma bv_abs_srem_sext32_toNat_lt (x y : BitVec 32) (hne : y ≠ 0#32) :
    (bv_abs (sign_extend (m := 64) (BitVec.srem x y))).toNat <
      (bv_abs (sign_extend (m := 64) y)).toNat := by
  have hy_toInt_ne : y.toInt ≠ 0 := by
    intro h
    apply hne
    exact BitVec.eq_of_toInt_eq (by simpa using h)
  rw [bv_abs_toNat_eq_natAbs, bv_abs_toNat_eq_natAbs,
    toInt_signExtend32_64 (BitVec.srem x y), toInt_signExtend32_64 y]
  rw [BitVec.toInt_srem, Int.natAbs_tmod]
  exact Nat.mod_lt _ (Int.natAbs_pos.mpr hy_toInt_ne)

private lemma sext32_sdiv_mul_add_srem
    (x y : BitVec 32) (hne : y ≠ 0#32)
    (hno : ¬ (x = BitVec.intMin 32 ∧ y = -1#32)) :
    sign_extend (m := 64) (BitVec.sdiv x y) * sign_extend (m := 64) y +
      sign_extend (m := 64) (BitVec.srem x y) = sign_extend (m := 64) x := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, BitVec.toInt_mul]
  repeat rw [toInt_signExtend32_64]
  have hne_pair : x ≠ BitVec.intMin 32 ∨ y ≠ -1#32 := by
    by_cases hx : x = BitVec.intMin 32
    · right
      intro hy
      exact hno ⟨hx, hy⟩
    · left
      exact hx
  have hq_int : (BitVec.sdiv x y).toInt = x.toInt.tdiv y.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne x y hne_pair
  have hr_int : (BitVec.srem x y).toInt = x.toInt.tmod y.toInt :=
    BitVec.toInt_srem x y
  have hsum_eq :
      (BitVec.sdiv x y).toInt * y.toInt + (BitVec.srem x y).toInt = x.toInt := by
    rw [hq_int, hr_int]
    have h := Int.tmod_add_mul_tdiv x.toInt y.toInt
    linarith
  have hq_lo : -(2^31 : Int) ≤ (BitVec.sdiv x y).toInt := by
    have := @BitVec.le_toInt 32 (BitVec.sdiv x y)
    simpa using this
  have hq_hi : (BitVec.sdiv x y).toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 (BitVec.sdiv x y)
    simpa using this
  have hy_lo : -(2^31 : Int) ≤ y.toInt := by
    have := @BitVec.le_toInt 32 y
    simpa using this
  have hy_hi : y.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 y
    simpa using this
  have hprod_lo : -(2^63 : Int) ≤ (BitVec.sdiv x y).toInt * y.toInt := by
    nlinarith
  have hprod_hi : (BitVec.sdiv x y).toInt * y.toInt < 2^63 := by
    nlinarith
  have hprod_bmod :
      ((BitVec.sdiv x y).toInt * y.toInt).bmod (2^64) =
        (BitVec.sdiv x y).toInt * y.toInt := by
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤ (BitVec.sdiv x y).toInt * y.toInt
      have h : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h]
      exact hprod_lo
    · show (BitVec.sdiv x y).toInt * y.toInt < ((((2^64 : Nat) : Int) + 1) / 2)
      have h : ((((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int)) := by decide
      rw [h]
      exact hprod_hi
  have hx_lo : -(2^31 : Int) ≤ x.toInt := by
    have := @BitVec.le_toInt 32 x
    simpa using this
  have hx_hi : x.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 x
    simpa using this
  have hsum_bmod :
      ((BitVec.sdiv x y).toInt * y.toInt + (BitVec.srem x y).toInt).bmod (2^64) =
        (BitVec.sdiv x y).toInt * y.toInt + (BitVec.srem x y).toInt := by
    rw [hsum_eq]
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤ x.toInt
      have h : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h]
      linarith
    · show x.toInt < ((((2^64 : Nat) : Int) + 1) / 2)
      have h : ((((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int)) := by decide
      rw [h]
      linarith
  rw [hprod_bmod, hsum_bmod, hsum_eq]

private lemma change_divisor_w_value_of_zero (x : BitVec 32) :
    change_divisor_w_value (sign_extend (m := 64) x)
      (sign_extend (m := 64) (0#32)) = 0#64 := by
  unfold change_divisor_w_value sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma change_divisor_w_value_of_overflow :
    change_divisor_w_value
        (sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32))
        (sign_extend (m := 64) (-1#32 : BitVec 32)) = 1#64 := by
  unfold change_divisor_w_value sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma change_divisor_w_value_of_normal (x y : BitVec 32)
    (hno : ¬ (x = BitVec.intMin 32 ∧ y = -1#32)) :
    change_divisor_w_value (sign_extend (m := 64) x)
      (sign_extend (m := 64) y) = sign_extend (m := 64) y := by
  unfold change_divisor_w_value sign_extend Sail.BitVec.signExtend
  bv_decide

-- ----------------------------------------------------------------------------
-- Case helpers for sail_divw_value / sail_remw_value
-- ----------------------------------------------------------------------------

/-- `sail_divw_value` returns `-1` when the low-32-bit divisor is zero. -/
private theorem sail_divw_value_of_zero (dividend divisor : BitVec 64)
    (h : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_divw_value dividend divisor false = (-1 : BitVec 64) := by
  unfold sail_divw_value
  simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toInt_zero,
             show ((0 : Int) == 0) = true from rfl,
             show LeanRV64D.Functions.not false = true from rfl, Bool.true_and,
             show ((-1 : Int) ≥b (2 ^i (31 : Int))) = false from by decide]
  decide

/-- `sail_remw_value` returns `sign_extend(rs1_low)` when the divisor low-32 is zero. -/
private theorem sail_remw_value_of_zero (dividend divisor : BitVec 64)
    (h : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_remw_value dividend divisor false =
      sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) := by
  unfold sail_remw_value
  simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toInt_zero,
             show ((0 : Int) == 0) = true from rfl]
  rw [trunc32_eq_intCast]
  congr 1
  exact BitVec.ofInt_toInt

/-- `sail_divw_value` returns `sign_extend(i32::MIN)` in the signed-overflow case. -/
private theorem sail_divw_value_of_overflow (dividend divisor : BitVec 64)
    (hsd : Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32)
    (hsv : Sail.BitVec.extractLsb divisor 31 0 = -1#32) :
    sail_divw_value dividend divisor false =
      sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32) := by
  unfold sail_divw_value
  simp only [hsd, hsv, Bool.false_eq_true, ↓reduceIte,
             /- show (BitVec.toInt (BitVec.intMin 32) == (0 : Int)) = false from by decide, -/
             show (BitVec.toInt (-1#32) == (0 : Int)) = false from by decide,
             show LeanRV64D.Functions.not false = true from rfl, Bool.true_and,
             show (Int.tdiv (BitVec.toInt (BitVec.intMin 32)) (BitVec.toInt (-1#32))
                    ≥b (2 ^i (31 : Int))) = true from by decide]
  decide

/-- `sail_remw_value` returns `0` in the signed-overflow case. -/
private theorem sail_remw_value_of_overflow (dividend divisor : BitVec 64)
    (hsd : Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32)
    (hsv : Sail.BitVec.extractLsb divisor 31 0 = -1#32) :
    sail_remw_value dividend divisor false = 0#64 := by
  unfold sail_remw_value
  simp only [hsd, hsv, Bool.false_eq_true, ↓reduceIte,
             show (BitVec.toInt (-1#32) == (0 : Int)) = false from by decide]
  decide

/-- Helper: `sign_extend(i32::MIN)` equals `change_divisor_w_value`'s i32MinSext. -/
private lemma i32MinSext_eq : sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32) =
    -((1 : BitVec 64) <<< 31) := by decide

/-- `sail_divw_value` agrees with 32-bit sdiv (sign-extended) in normal case. -/
private theorem sail_divw_value_of_normal (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32)
    (hno_ovf : ¬ (Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
                  Sail.BitVec.extractLsb divisor 31 0 = -1#32)) :
    sail_divw_value dividend divisor false =
      sign_extend (m := 64)
        (BitVec.sdiv (Sail.BitVec.extractLsb dividend 31 0)
                     (Sail.BitVec.extractLsb divisor 31 0)) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hy32_toInt_ne : y32.toInt ≠ 0 := by
    intro h; apply hne; exact BitVec.eq_of_toInt_eq (by simpa using h)
  have hne_pair : x32 ≠ BitVec.intMin 32 ∨ y32 ≠ -1#32 := by
    by_cases hx : x32 = BitVec.intMin 32
    · right; intro hy; apply hno_ovf; exact ⟨hx, hy⟩
    · left; exact hx
  have hsdiv_toInt : (BitVec.sdiv x32 y32).toInt = Int.tdiv x32.toInt y32.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne x32 y32 hne_pair
  have hbnd_hi : Int.tdiv x32.toInt y32.toInt < 2^31 := by
    rw [← hsdiv_toInt]
    have := @BitVec.toInt_lt 32 (BitVec.sdiv x32 y32); simpa using this
  unfold sail_divw_value
  rw [← hx32, ← hy32]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzero_false : (y32.toInt == (0 : Int)) = false :=
    decide_eq_false hy32_toInt_ne
  simp only [hzero_false]
  have hge_false : (Int.tdiv x32.toInt y32.toInt ≥b (2 ^i (31 : Int))) = false := by
    show decide _ = false; apply decide_eq_false; push_neg
    simpa using hbnd_hi
  simp only [Bool.false_eq_true, show LeanRV64D.Functions.not false = true from rfl, Bool.true_and,
             hge_false, ↓reduceIte]
  rw [trunc32_eq_intCast, ← hsdiv_toInt]
  congr 1
  exact BitVec.ofInt_toInt

/-- `sail_remw_value` agrees with 32-bit srem (sign-extended) in normal case. -/
private theorem sail_remw_value_of_normal (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32) :
    sail_remw_value dividend divisor false =
      sign_extend (m := 64)
        (BitVec.srem (Sail.BitVec.extractLsb dividend 31 0)
                     (Sail.BitVec.extractLsb divisor 31 0)) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hy32_toInt_ne : y32.toInt ≠ 0 := by
    intro h; apply hne; exact BitVec.eq_of_toInt_eq (by simpa using h)
  unfold sail_remw_value
  rw [← hx32, ← hy32]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzero_false : (y32.toInt == (0 : Int)) = false :=
    decide_eq_false hy32_toInt_ne
  simp only [hzero_false]
  rw [trunc32_eq_intCast, ← BitVec.toInt_srem]
  congr 1
  exact BitVec.ofInt_toInt

-- ----------------------------------------------------------------------------
-- Sign-fixup helpers for 32-bit embedded values
-- ----------------------------------------------------------------------------

/-- For sign-extended 32-bit `x`, applying the sign-fixup `(bv_abs ∘ sign_extend) ^^^ sd.sshiftRight 63 - ...`
recovers `sign_extend x`. Analog of `srem_xor_sub_sign_eq_srem` for DIVW. -/
private theorem sext32_xor_sub_sign_eq_sext32
    (val x32 y32 : BitVec 32)
    (hval_srem : val = BitVec.srem x32 y32)
    (hne : y32 ≠ 0#32) :
    (bv_abs (sign_extend (m := 64) val) ^^^
      (sign_extend (m := 64) x32).sshiftRight 63) -
      (sign_extend (m := 64) x32).sshiftRight 63 =
    sign_extend (m := 64) val := by
  by_cases hzero : val = 0#32
  · rw [hzero]
    unfold sign_extend Sail.BitVec.signExtend bv_abs
    bv_decide
  · have hsrem_ne : BitVec.srem x32 y32 ≠ 0#32 := by
      intro hs
      exact hzero (hval_srem.trans hs)
    have hmsb_eq : val.msb = x32.msb := by
      rw [hval_srem, BitVec.msb_srem]
      simp [hsrem_ne]
    have hssr_eq :
        (sign_extend (m := 64) val).sshiftRight 63 =
        (sign_extend (m := 64) x32).sshiftRight 63 :=
      sshiftRight63_signExtend_eq_of_msb_eq val x32 hmsb_eq
    rw [← hssr_eq]
    exact x_eq_bv_abs_xor_sub_sign (sign_extend (m := 64) val)

private lemma signfix31_bv_abs_sext32_eq_self (x : BitVec 32) :
    (bv_abs (sign_extend (m := 64) x) ^^^
      (sign_extend (m := 64) x).sshiftRight 31) -
      (sign_extend (m := 64) x).sshiftRight 31 =
    sign_extend (m := 64) x := by
  unfold sign_extend Sail.BitVec.signExtend
  rw [sshiftRight31_eq_63_of_sext32]
  exact x_eq_bv_abs_xor_sub_sign (x.signExtend 64)

private theorem sext32_xor_sub_sign31_eq_sext32
    (val x32 y32 : BitVec 32)
    (hval_srem : val = BitVec.srem x32 y32)
    (hne : y32 ≠ 0#32) :
    (bv_abs (sign_extend (m := 64) val) ^^^
      (sign_extend (m := 64) x32).sshiftRight 31) -
      (sign_extend (m := 64) x32).sshiftRight 31 =
    sign_extend (m := 64) val := by
  have hssr :
      (sign_extend (m := 64) x32).sshiftRight 31 =
      (sign_extend (m := 64) x32).sshiftRight 63 := by
    unfold sign_extend Sail.BitVec.signExtend
    exact sshiftRight31_eq_63_of_sext32 x32
  rw [hssr]
  exact sext32_xor_sub_sign_eq_sext32 val x32 y32 hval_srem hne

-- ----------------------------------------------------------------------------
-- The five honest-advice guard lemmas
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertValidDiv0` on the sign-extended divisor.**

When the *sign-extended* divisor `v5` is zero, the RISC-V DIVW spec
fixes the quotient as `-1` (32-bit, sign-extended to 64). Under honest
advice `q = sail_divw_value dividend divisor false`, the conjunction
`sext_divisor = 0 ∧ q ≠ -1` is impossible. -/
theorem hguard_div0_of_honest_w (dividend divisor : BitVec 64) :
    ¬ (sext_divisor_w divisor = 0#64 ∧
       q_w dividend divisor ≠ (-1 : BitVec 64)) := by
  rintro ⟨hdiv, hq⟩
  apply hq
  apply sail_divw_value_of_zero dividend divisor
  exact eq_zero_of_signExtend32_eq_zero _ hdiv

-- Extracting the low 32 bits of a 64-bit sign-extension of a 32-bit value
-- gives back the original 32-bit value.
-- (Already proved above as extractLsb_signExtend_32_64)

/-- **Guard 2 — `VirtualAssertEQ v3 v0` (32-bit quotient round-trip).**

The quotient produced by Sail's `execute_DIVW` is the result of
`sign_extend ∘ to_bits_truncate 32` applied to a 32-bit integer,
hence it satisfies the round-trip identity
`sign_extend (extractLsb q 31 0) = q`. -/
theorem hguard_q_fits_of_honest_w (dividend divisor : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (q_w dividend divisor) 31 0)
      = q_w dividend divisor := by
  unfold q_w sail_divw_value sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  bv_decide

-- WARNING: MISALIGNED — Rust inline sequence uses SRAI rem 31 but must be SRAI rem 32.
-- With shift 31 this theorem is FALSE: rs1_low = i32::MIN, rs2_low = 0 gives
-- rem = 2^31 and SRAI(2^31, 31) = 1 ≠ 0. See bug_reports/divw.md.
/-- **Guard 3 — `VirtualAssertEQ v4 x0` (`|rem|` fits in u32).**

Honest `|rem|` is `(sail_remw_value … as i32).unsigned_abs`, which is
a `u32` zero-extended into 64 bits. Its high 32 bits are zero, so
arithmetic-shift-right by 32 yields `0#64`. -/
theorem hguard_rem_nonneg_of_honest_w (dividend divisor : BitVec 64) :
    shift_bits_right_arith (rem_w dividend divisor) (32 : BitVec 6) = 0#64 := by
  unfold rem_w sail_remw_value shift_bits_right_arith
  simp [Sail.BitVec.toNatInt]
  exact bv_abs_sext32_sshiftRight32 _

/-- **Guard 4 — `VirtualAssertEQ v3 v6` (32-bit division equation).**

`q · adj + signed_rem = sext(rs1)` at 32-bit width, where
`signed_rem = (rem XOR sign(sext_dividend)) - sign(sext_dividend)` is
the two's-complement sign-fixup of `|rem|`. The DIVW analogue of
`hguard_quotient_product_of_honest`, but with `shamt = 31` and the
sign-extended dividend in place of the real `rs1`. -/
theorem hguard_quotient_product_of_honest_w (dividend divisor : BitVec 64) :
    let q   := q_w dividend divisor
    let rem := rem_w dividend divisor
    let sd  := sext_dividend_w dividend
    let adj := adj_w dividend divisor
    q * adj +
      ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31)
      = sd := by
  unfold q_w rem_w sext_dividend_w adj_w sext_divisor_w
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · have hq : sail_divw_value dividend divisor false = (-1 : BitVec 64) := by
      apply sail_divw_value_of_zero dividend divisor
      rw [← hy32]
      exact hzero
    have hsail_rem :
        sail_remw_value dividend divisor false = sign_extend (m := 64) x32 := by
      rw [sail_remw_value_of_zero dividend divisor (by rw [← hy32]; exact hzero),
        ← hx32]
    have hadj :
        change_divisor_w_value (sign_extend (m := 64) x32)
          (sign_extend (m := 64) y32) = 0#64 := by
      rw [hzero]
      exact change_divisor_w_value_of_zero x32
    rw [hq, hsail_rem, hadj]
    dsimp
    rw [BitVec.zero_add]
    exact signfix31_bv_abs_sext32_eq_self x32
  · by_cases hovf : x32 = BitVec.intMin 32 ∧ y32 = -1#32
    · have hq :
          sail_divw_value dividend divisor false =
            sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32) := by
        apply sail_divw_value_of_overflow
        · rw [← hx32]
          exact hovf.1
        · rw [← hy32]
          exact hovf.2
      have hsail_rem : sail_remw_value dividend divisor false = 0#64 := by
        apply sail_remw_value_of_overflow
        · rw [← hx32]
          exact hovf.1
        · rw [← hy32]
          exact hovf.2
      have hadj :
          change_divisor_w_value (sign_extend (m := 64) x32)
            (sign_extend (m := 64) y32) = 1#64 := by
        rw [hovf.1, hovf.2]
        exact change_divisor_w_value_of_overflow
      rw [hq, hsail_rem, hadj, hovf.1]
      decide
    · have hne_divisor : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32 := by
        intro h
        exact hzero (hy32.trans h)
      have hno_orig :
          ¬ (Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
              Sail.BitVec.extractLsb divisor 31 0 = -1#32) := by
        rintro ⟨hd, hv⟩
        exact hovf ⟨by rw [hx32, hd], by rw [hy32, hv]⟩
      have hq :
          sail_divw_value dividend divisor false =
            sign_extend (m := 64) (BitVec.sdiv x32 y32) := by
        rw [sail_divw_value_of_normal dividend divisor hne_divisor hno_orig,
          ← hx32, ← hy32]
      have hsail_rem :
          sail_remw_value dividend divisor false =
            sign_extend (m := 64) (BitVec.srem x32 y32) := by
        rw [sail_remw_value_of_normal dividend divisor hne_divisor, ← hx32, ← hy32]
      have hadj :
          change_divisor_w_value (sign_extend (m := 64) x32)
            (sign_extend (m := 64) y32) = sign_extend (m := 64) y32 :=
        change_divisor_w_value_of_normal x32 y32 hovf
      rw [hq, hsail_rem, hadj]
      dsimp
      rw [sext32_xor_sub_sign31_eq_sext32 (BitVec.srem x32 y32) x32 y32 rfl hzero]
      exact sext32_sdiv_mul_add_srem x32 y32 hzero hovf

/-- **Guard 5 — `VirtualAssertValidUnsignedRemainder`.**

Under honest advice, either the (sign-extended) adjusted divisor's
absolute value is zero, or `|rem|` is strictly less than `|adj|`
unsigned. The `XOR + SUB` with `shamt = 31` computes `|adj|` via
the two's-complement abs trick. -/
theorem hguard_rem_bound_of_honest_w (dividend divisor : BitVec 64) :
    let rem := rem_w dividend divisor
    let adj := adj_w dividend divisor
    ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat := by
  unfold rem_w adj_w sext_dividend_w sext_divisor_w
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · left
    have hadj :
        change_divisor_w_value (sign_extend (m := 64) x32)
          (sign_extend (m := 64) y32) = 0#64 := by
      rw [hzero]
      exact change_divisor_w_value_of_zero x32
    rw [hadj]
    decide
  · by_cases hovf : x32 = BitVec.intMin 32 ∧ y32 = -1#32
    · right
      have hsail_rem : sail_remw_value dividend divisor false = 0#64 := by
        apply sail_remw_value_of_overflow
        · rw [← hx32]
          exact hovf.1
        · rw [← hy32]
          exact hovf.2
      have hadj :
          change_divisor_w_value (sign_extend (m := 64) x32)
            (sign_extend (m := 64) y32) = 1#64 := by
        rw [hovf.1, hovf.2]
        exact change_divisor_w_value_of_overflow
      rw [hsail_rem, hadj]
      decide
    · right
      have hne_divisor : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32 := by
        intro h
        exact hzero (hy32.trans h)
      have hsail_rem :
          sail_remw_value dividend divisor false =
            sign_extend (m := 64) (BitVec.srem x32 y32) := by
        rw [sail_remw_value_of_normal dividend divisor hne_divisor, ← hx32, ← hy32]
      have hadj :
          change_divisor_w_value (sign_extend (m := 64) x32)
            (sign_extend (m := 64) y32) = sign_extend (m := 64) y32 :=
        change_divisor_w_value_of_normal x32 y32 hovf
      rw [hsail_rem, hadj, xor_sub_sign31_sext32_eq_bv_abs y32]
      exact bv_abs_srem_sext32_toNat_lt x32 y32 hzero

-- ----------------------------------------------------------------------------
-- Soundness uniqueness
-- ----------------------------------------------------------------------------

/-- **Soundness uniqueness.** If the five guards hold for some advice
`(q, rem)` and the sign-extension/adjustment relations are honestly
realised by `(sd, sv, adj)`, then `(q, rem)` is the unique honest
advice pair `(sail_divw_value, bv_abs sail_remw_value)`.

DIVW analogue of `advice_unique_of_guards` from `Div_math.lean`, but
with five guards (DIV has four — DIVW adds the `|rem|` fits-in-u32 check).
The proof plan splits on `sv = 0`, the overflow pair `(i32::MIN, -1)`,
and the normal case. -/
theorem advice_unique_of_guards_w
    (dividend divisor q rem adj : BitVec 64)
    (sd sv : BitVec 64)
    (hsd : sd = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0))
    (hsv : sv = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0))
    (hadj : adj = change_divisor_w_value sd sv)
    (h1 : ¬ (sv = 0#64 ∧ q ≠ (-1 : BitVec 64)))
    (h2 : sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q)
    (h3 : shift_bits_right_arith rem (32 : BitVec 6) = 0#64)
    (h4 : q * adj +
            ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31)
          = sd)
    (h5 : ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
            rem.toNat <
              ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) :
    q = sail_divw_value dividend divisor false ∧
    rem = bv_abs (sail_remw_value dividend divisor false) := by
  sorry

end
