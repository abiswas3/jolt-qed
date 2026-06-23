import JoltBytecode.Derived
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.DivwProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `divwProgram` (advice-verified DIVW)

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
remainder advice supplied to `divwProgram` is `bv_abs (sail_remw_value …)`,
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
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend]
  have hi32 : i < 32 := by omega
  have hi64 : i < 64 := by omega
  simp [hi32, hi64]

private lemma extractLsb_sail_signExtend_32_64 (x : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0 = x := by
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32_bool : (i <b 32) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  have hi64_bool : (i <b 64) = true := by
    have : i < 64 := by omega
    simpa only [Nat.blt_eq, decide_eq_true_eq] using this
  simp (disch := omega) only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend,
    Nat.reduceSub, Nat.reduceAdd, hi32_bool, hi64_bool, Bool.true_and, Nat.zero_add,
    if_pos]

/-- For a sign-extended 32-bit value, `sshiftRight 31 = sshiftRight 63`.
Both produce the sign-broadcast (all-zeros or all-ones). -/
private lemma sshiftRight31_eq_63_of_sext32 (x : BitVec 32) :
    (x.signExtend 64 : BitVec 64).sshiftRight 31 =
    (x.signExtend 64 : BitVec 64).sshiftRight 63 := by
  ext i hi
  rw [BitVec.getElem_sshiftRight, BitVec.getElem_sshiftRight]
  have hi64 : ¬ 64 ≤ i := by omega
  by_cases hi0 : i = 0
  · subst i
    simp [hi64, BitVec.getLsbD_signExtend,
      ← BitVec.getLsbD_eq_getElem, BitVec.msb_eq_getLsbD_last]
  · have h31_lo : ¬ 31 + i < 32 := by omega
    by_cases h31_hi : 31 + i < 64
    · have h63_hi : ¬ 63 + i < 64 := by omega
      simp [hi64, h31_hi, h31_lo, h63_hi, BitVec.getLsbD_signExtend,
        ← BitVec.getLsbD_eq_getElem, BitVec.msb_eq_getLsbD_last]
    · have h63_hi : ¬ 63 + i < 64 := by omega
      simp [hi64, h31_hi, h63_hi]

/-- `bv_abs` of a sign-extended 32-bit value, arithmetic-shifted right by 32,
is zero — i.e., the absolute value fits in u32. -/
private lemma bv_abs_sext32_sshiftRight32 (x : BitVec 32) :
    (bv_abs (sign_extend (m := 64) x)).sshiftRight 32 = 0#64 := by
  let v := bv_abs (sign_extend (m := 64) x)
  have hsext_toInt : (sign_extend (m := 64) x).toInt = x.toInt := by
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
  have hv_le : v.toNat ≤ 2^31 := by
    dsimp [v]
    rw [bv_abs_toNat_eq_natAbs, hsext_toInt]
    have hlo : -(2^31 : Int) ≤ x.toInt := by
      have := @BitVec.le_toInt 32 x
      simpa using this
    have hhi : x.toInt < 2^31 := by
      have := @BitVec.toInt_lt 32 x
      simpa using this
    have h : (x.toInt.natAbs : Int) ≤ 2^31 := by
      by_cases hx : 0 ≤ x.toInt
      · rw [Int.natAbs_of_nonneg hx]
        omega
      · push_neg at hx
        have hnn : 0 ≤ -x.toInt := by omega
        have hn_eq : (x.toInt.natAbs : Int) = -x.toInt := by
          have := Int.natAbs_of_nonneg hnn
          rw [Int.natAbs_neg] at this
          exact this
        rw [hn_eq]
        omega
    exact_mod_cast h
  have hv_msb : v.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    have hle : 2 * v.toNat ≤ 2 * 2^31 := Nat.mul_le_mul_left 2 hv_le
    exact lt_of_le_of_lt hle (by norm_num)
  change v.sshiftRight 32 = 0#64
  rw [BitVec.sshiftRight_eq_of_msb_false hv_msb]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (lt_of_le_of_lt hv_le (by norm_num))

private lemma eq_zero_of_signExtend32_eq_zero (x : BitVec 32)
    (h : sign_extend (m := 64) x = 0#64) : x = 0#32 := by
  unfold sign_extend Sail.BitVec.signExtend at h
  have hlow := congrArg (fun z : BitVec 64 => z.extractLsb 31 0) h
  simpa [extractLsb_signExtend_32_64] using hlow

private lemma sshiftRight63_signExtend_eq_of_msb_eq (x y : BitVec 32)
    (h : x.msb = y.msb) :
    (sign_extend (m := 64) x).sshiftRight 63 =
    (sign_extend (m := 64) y).sshiftRight 63 := by
  unfold sign_extend Sail.BitVec.signExtend
  ext i hi
  rw [BitVec.getElem_sshiftRight, BitVec.getElem_sshiftRight]
  have hi64 : ¬ 64 ≤ i := by omega
  by_cases hi0 : i = 0
  · subst i
    simp [hi64, BitVec.getLsbD_signExtend,
      ← BitVec.getLsbD_eq_getElem, BitVec.msb_eq_getLsbD_last, h]
    simpa [BitVec.msb_eq_getLsbD_last] using h
  · have h63_hi : ¬ 63 + i < 64 := by omega
    simp [hi64, h63_hi, h]
    simpa [BitVec.msb_eq_getLsbD_last, ← BitVec.getLsbD_eq_getElem,
      BitVec.getLsbD_signExtend] using h

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
  have hzero : sign_extend (m := 64) (0#32 : BitVec 32) = 0#64 := by
    unfold sign_extend Sail.BitVec.signExtend
    decide
  rw [hzero]
  unfold change_divisor_w_value
  rw [if_neg (by
    intro h
    exact (by decide : (0#64 : BitVec 64) ≠ -1) h.2)]

private lemma change_divisor_w_value_of_overflow :
    change_divisor_w_value
        (sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32))
        (sign_extend (m := 64) (-1#32 : BitVec 32)) = 1#64 := by
  have hmin : sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32) =
      -((1 : BitVec 64) <<< 31) := by
    decide
  have hneg : sign_extend (m := 64) (-1#32 : BitVec 32) = (-1 : BitVec 64) := by
    unfold sign_extend Sail.BitVec.signExtend
    decide
  rw [hmin, hneg]
  unfold change_divisor_w_value
  rw [if_pos (by constructor <;> rfl)]
  rfl

private lemma change_divisor_w_value_of_normal (x y : BitVec 32)
    (hno : ¬ (x = BitVec.intMin 32 ∧ y = -1#32)) :
    change_divisor_w_value (sign_extend (m := 64) x)
      (sign_extend (m := 64) y) = sign_extend (m := 64) y := by
  unfold change_divisor_w_value sign_extend Sail.BitVec.signExtend
  rw [if_neg]
  intro hoverflow
  apply hno
  rcases hoverflow with ⟨hx, hy⟩
  constructor
  · have hxlow := congrArg (fun z : BitVec 64 => z.extractLsb 31 0) hx
    simpa [extractLsb_signExtend_32_64] using hxlow
  · have hylow := congrArg (fun z : BitVec 64 => z.extractLsb 31 0) hy
    simpa [extractLsb_signExtend_32_64] using hylow

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
    unfold bv_abs
    have hzero64 : sign_extend (m := 64) (0#32 : BitVec 32) = 0#64 := by
      decide
    rw [hzero64]
    simp only [BitVec.msb_zero, ↓reduceIte]
    by_cases hx : x32.msb = false
    · have hsign :
          (sign_extend (m := 64) x32).sshiftRight 63 =
          (sign_extend (m := 64) (0#32 : BitVec 32)).sshiftRight 63 := by
        exact sshiftRight63_signExtend_eq_of_msb_eq x32 0#32 (by simp [hx])
      rw [hsign]
      decide
    · have hxtrue : x32.msb = true := by
        cases hxv : x32.msb <;> simp_all
      have hsign :
          (sign_extend (m := 64) x32).sshiftRight 63 =
          (sign_extend (m := 64) (-1#32 : BitVec 32)).sshiftRight 63 := by
        exact sshiftRight63_signExtend_eq_of_msb_eq x32 (-1#32) (by
          rw [hxtrue]
          decide)
      rw [hsign]
      decide
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
  unfold q_w sail_divw_value
  rw [extractLsb_sail_signExtend_32_64]

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

private theorem sshiftRight63_of_msb_false_w {x : BitVec 64}
    (h : x.msb = false) : x.sshiftRight 63 = 0#64 := by
  rw [BitVec.sshiftRight_eq_of_msb_false h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
  have hx : 2 * x.toNat < 2 ^ 64 := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have : x.toNat / 2^63 = 0 := by omega
  rw [Nat.shiftRight_eq_div_pow]
  exact this

private theorem sshiftRight63_of_msb_true_w {x : BitVec 64}
    (h : x.msb = true) : x.sshiftRight 63 = -1#64 := by
  rw [BitVec.sshiftRight_eq_of_msb_true h]
  have hnotmsb : (~~~x).msb = false := by
    rw [BitVec.msb_not]
    simp [h]
  have hush_zero : (~~~x) >>> 63 = 0#64 := by
    rw [← BitVec.sshiftRight_eq_of_msb_false hnotmsb]
    exact sshiftRight63_of_msb_false_w hnotmsb
  rw [hush_zero]
  decide

private lemma msb_signExtend32_64 (x : BitVec 32) :
    (sign_extend (m := 64) x).msb = x.msb := by
  unfold sign_extend Sail.BitVec.signExtend
  rw [BitVec.msb_eq_getLsbD_last]
  rw [BitVec.getLsbD_signExtend]
  simp (disch := omega) only [Nat.reduceSub, if_neg]
  norm_num

private theorem rem_from_sign_fixup_eq_w (rem y : BitVec 64)
    (h : (rem ^^^ y.sshiftRight 63) - y.sshiftRight 63 = y) :
    rem = bv_abs y := by
  unfold bv_abs
  by_cases hmsb : y.msb = true
  · rw [if_pos hmsb]
    rw [sshiftRight63_of_msb_true_w hmsb] at h
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes] at h
    rw [show BitVec.allOnes 64 = -1#64 from by decide, BitVec.sub_neg] at h
    rw [← BitVec.neg_eq_not_add] at h
    rw [BitVec.neg_eq_iff_eq_neg] at h
    exact h
  · have hf : y.msb = false := by
      cases h' : y.msb
      · rfl
      · exact (hmsb h').elim
    rw [if_neg hmsb]
    rw [sshiftRight63_of_msb_false_w hf, BitVec.xor_zero, BitVec.sub_zero] at h
    exact h

private theorem rem_from_signfix31_eq_sext32 (rem : BitVec 64) (x : BitVec 32)
    (h : (rem ^^^ (sign_extend (m := 64) x).sshiftRight 31) -
          (sign_extend (m := 64) x).sshiftRight 31 =
          sign_extend (m := 64) x) :
    rem = bv_abs (sign_extend (m := 64) x) := by
  have hshift :
      (sign_extend (m := 64) x).sshiftRight 31 =
      (sign_extend (m := 64) x).sshiftRight 63 := by
    unfold sign_extend Sail.BitVec.signExtend
    exact sshiftRight31_eq_63_of_sext32 x
  rw [hshift] at h
  exact rem_from_sign_fixup_eq_w rem (sign_extend (m := 64) x) h

private theorem bv64_eq_zero_of_toNat_lt_one (x : BitVec 64) (h : x.toNat < 1) :
    x = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

private theorem int_uniqueness_step_w {a b q r : Int} (hb : b ≠ 0)
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

private theorem signed_rem_toInt_sext32 {rem : BitVec 64} (x : BitVec 32)
    (hrem_msb : rem.msb = false) :
    ((rem ^^^ (sign_extend (m := 64) x).sshiftRight 31) -
        (sign_extend (m := 64) x).sshiftRight 31).toInt
      = if x.msb then -(rem.toNat : Int) else (rem.toNat : Int) := by
  have hshift :
      (sign_extend (m := 64) x).sshiftRight 31 =
      (sign_extend (m := 64) x).sshiftRight 63 := by
    unfold sign_extend Sail.BitVec.signExtend
    exact sshiftRight31_eq_63_of_sext32 x
  rw [hshift]
  by_cases hx : x.msb = true
  · have hsext_msb : (sign_extend (m := 64) x).msb = true := by
      rw [msb_signExtend32_64, hx]
    rw [if_pos hx, sshiftRight63_of_msb_true_w hsext_msb]
    rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from by decide,
        BitVec.xor_allOnes]
    rw [show BitVec.allOnes 64 = -1#64 from by decide, BitVec.sub_neg]
    rw [← BitVec.neg_eq_not_add]
    rw [BitVec.toInt_neg, BitVec.toInt_eq_toNat_of_msb hrem_msb]
    have h_bound : (rem.toNat : Int) < 2^63 := by
      have : 2 * rem.toNat < 2^64 := BitVec.msb_eq_false_iff_two_mul_lt.mp hrem_msb
      exact_mod_cast (by omega : rem.toNat < 2^63)
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤ -(rem.toNat : Int)
      have h64 : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h64]
      omega
    · show -(rem.toNat : Int) < (((2^64 : Nat) : Int) + 1) / 2
      have h64 : (((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int) := by decide
      rw [h64]
      have : 0 ≤ (rem.toNat : Int) := Int.natCast_nonneg _
      omega
  · have hx_f : x.msb = false := by
      cases h : x.msb
      · rfl
      · exact (hx h).elim
    have hsext_msb : (sign_extend (m := 64) x).msb = false := by
      rw [msb_signExtend32_64, hx_f]
    rw [if_neg hx, sshiftRight63_of_msb_false_w hsext_msb,
      BitVec.xor_zero, BitVec.sub_zero]
    exact BitVec.toInt_eq_toNat_of_msb hrem_msb

private lemma int32_toInt_natAbs_le (x : BitVec 32) :
    x.toInt.natAbs ≤ 2^31 := by
  have hlo : -(2^31 : Int) ≤ x.toInt := by
    have := @BitVec.le_toInt 32 x
    simpa using this
  have hhi : x.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 x
    simpa using this
  have h : (x.toInt.natAbs : Int) ≤ 2^31 := by
    by_cases hx : 0 ≤ x.toInt
    · rw [Int.natAbs_of_nonneg hx]
      omega
    · push_neg at hx
      have hnn : 0 ≤ -x.toInt := by omega
      have hn_eq : (x.toInt.natAbs : Int) = -x.toInt := by
        have := Int.natAbs_of_nonneg hnn
        rw [Int.natAbs_neg] at this
        exact this
      rw [hn_eq]
      omega
  exact_mod_cast h

private lemma bv_abs_sext32_toNat_le_pow31 (x : BitVec 32) :
    (bv_abs (sign_extend (m := 64) x)).toNat ≤ 2^31 := by
  rw [bv_abs_toNat_eq_natAbs, toInt_signExtend32_64]
  exact int32_toInt_natAbs_le x

private lemma bv_abs_sext32_toNat_pos_of_ne_zero (x : BitVec 32) (hne : x ≠ 0#32) :
    0 < (bv_abs (sign_extend (m := 64) x)).toNat := by
  rw [bv_abs_toNat_eq_natAbs, toInt_signExtend32_64]
  apply Int.natAbs_pos.mpr
  intro h
  apply hne
  exact BitVec.eq_of_toInt_eq (by simpa using h)

private theorem advice_unique_normal_w
    (x y : BitVec 32) (q rem : BitVec 64)
    (hy_ne : y ≠ 0#32)
    (hno : ¬ (x = BitVec.intMin 32 ∧ y = -1#32))
    (hq_fit : sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q)
    (hprod : q * sign_extend (m := 64) y +
            ((rem ^^^ (sign_extend (m := 64) x).sshiftRight 31) -
              (sign_extend (m := 64) x).sshiftRight 31)
          = sign_extend (m := 64) x)
    (hbnd : rem.toNat < (bv_abs (sign_extend (m := 64) y)).toNat) :
    q = sign_extend (m := 64) (BitVec.sdiv x y) ∧
    rem = bv_abs (sign_extend (m := 64) (BitVec.srem x y)) := by
  have hy_toInt_ne : (sign_extend (m := 64) y).toInt ≠ 0 := by
    rw [toInt_signExtend32_64]
    intro h
    apply hy_ne
    exact BitVec.eq_of_toInt_eq (by simpa using h)
  have hne_pair : x ≠ BitVec.intMin 32 ∨ y ≠ -1#32 := by
    by_cases hx : x = BitVec.intMin 32
    · right
      intro hy
      exact hno ⟨hx, hy⟩
    · left
      exact hx
  set q32 := Sail.BitVec.extractLsb q 31 0 with hq32
  have hq_toInt : q.toInt = q32.toInt := by
    rw [← hq_fit, toInt_signExtend32_64]
  have hq_lo : -(2^31 : Int) ≤ q32.toInt := by
    have := @BitVec.le_toInt 32 q32
    simpa using this
  have hq_hi : q32.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 q32
    simpa using this
  have hy_lo : -(2^31 : Int) ≤ y.toInt := by
    have := @BitVec.le_toInt 32 y
    simpa using this
  have hy_hi : y.toInt < 2^31 := by
    have := @BitVec.toInt_lt 32 y
    simpa using this
  have hprod_lo :
      -(2^63 : Int) ≤ q.toInt * (sign_extend (m := 64) y).toInt := by
    rw [hq_toInt, toInt_signExtend32_64]
    nlinarith
  have hprod_hi :
      q.toInt * (sign_extend (m := 64) y).toInt < 2^63 := by
    rw [hq_toInt, toInt_signExtend32_64]
    nlinarith
  have hmul_toInt :
      (q * sign_extend (m := 64) y).toInt =
        q.toInt * (sign_extend (m := 64) y).toInt := by
    rw [BitVec.toInt_mul]
    apply Int.bmod_eq_of_le
    · show -(((2^64 : Nat) : Int) / 2) ≤
          q.toInt * (sign_extend (m := 64) y).toInt
      have h64 : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
      rw [h64]
      exact hprod_lo
    · show q.toInt * (sign_extend (m := 64) y).toInt <
          (((2^64 : Nat) : Int) + 1) / 2
      have h64 : ((((2^64 : Nat) : Int) + 1) / 2) = (2^63 : Int) := by decide
      rw [h64]
      exact hprod_hi
  have hrem_msb : rem.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    have hy_abs_le : (bv_abs (sign_extend (m := 64) y)).toNat ≤ 2^31 :=
      bv_abs_sext32_toNat_le_pow31 y
    have hrem_lt : rem.toNat < 2^63 := by
      have : rem.toNat < 2^31 := lt_of_lt_of_le hbnd hy_abs_le
      omega
    omega
  set s :=
    (rem ^^^ (sign_extend (m := 64) x).sshiftRight 31) -
      (sign_extend (m := 64) x).sshiftRight 31 with hs_def
  have h_signed_int :
      s.toInt = if x.msb then -(rem.toNat : Int) else (rem.toNat : Int) := by
    rw [hs_def]
    exact signed_rem_toInt_sext32 x hrem_msb
  have h_s_natAbs : s.toInt.natAbs = rem.toNat := by
    rw [h_signed_int]
    by_cases hx : x.msb
    · simp [hx, Int.natAbs_neg]
    · simp [hx]
  have h_s_sign_pos :
      0 ≤ (sign_extend (m := 64) x).toInt → 0 ≤ s.toInt := by
    intro hx_nonneg
    rw [h_signed_int]
    by_cases hxmsb : x.msb
    · simp [hxmsb]
      have hxneg := BitVec.toInt_neg_of_msb_true hxmsb
      rw [toInt_signExtend32_64] at hx_nonneg
      omega
    · simp [hxmsb]
  have h_s_sign_neg :
      (sign_extend (m := 64) x).toInt < 0 → s.toInt ≤ 0 := by
    intro hx_neg
    rw [h_signed_int]
    have hxmsb : x.msb = true := by
      by_contra hx_f
      push_neg at hx_f
      have h_msb_f : x.msb = false := by
        cases h' : x.msb
        · rfl
        · exact (hx_f h').elim
      have hx_nonneg := BitVec.toInt_nonneg_of_msb_false h_msb_f
      rw [toInt_signExtend32_64] at hx_neg
      omega
    simp [hxmsb]
  have h_s_abs : -(rem.toNat : Int) ≤ s.toInt ∧ s.toInt ≤ (rem.toNat : Int) := by
    rw [h_signed_int]
    by_cases hx : x.msb
    · simp [hx]
    · simp [hx]
  have hbnd_natAbs :
      rem.toNat < (sign_extend (m := 64) y).toInt.natAbs := by
    rw [← bv_abs_toNat_eq_natAbs]
    exact hbnd
  have h_rem_lt :
      (rem.toNat : Int) < ((sign_extend (m := 64) y).toInt.natAbs : Int) := by
    exact_mod_cast hbnd_natAbs
  have h_div_natAbs :
      ((sign_extend (m := 64) y).toInt.natAbs : Int) ≤ 2^31 := by
    rw [toInt_signExtend32_64]
    exact_mod_cast int32_toInt_natAbs_le y
  have hx_lo : -(2^31 : Int) ≤ (sign_extend (m := 64) x).toInt := by
    rw [toInt_signExtend32_64]
    have := @BitVec.le_toInt 32 x
    simpa using this
  have hx_hi : (sign_extend (m := 64) x).toInt < 2^31 := by
    rw [toInt_signExtend32_64]
    have := @BitVec.toInt_lt 32 x
    simpa using this
  have h_lift :
      (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt).bmod (2^64) =
        (sign_extend (m := 64) x).toInt := by
    have h_eq :
        (q * sign_extend (m := 64) y + s).toInt =
          (sign_extend (m := 64) x).toInt := by
      rw [hs_def, hprod]
    rw [BitVec.toInt_add, hmul_toInt] at h_eq
    exact h_eq
  have h_bmod_range_lo : -(((2^64 : Nat) : Int) / 2) ≤
      (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt).bmod (2^64) :=
    Int.le_bmod (by norm_num)
  have h_bmod_range_hi :
      (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt).bmod (2^64)
        < (((2^64 : Nat) : Int) + 1) / 2 :=
    Int.bmod_lt (by norm_num)
  have h_bdiv_decomp :
      (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt).bmod (2^64)
        = (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt)
          - (2^64 : Nat) *
              (q.toInt * (sign_extend (m := 64) y).toInt + s.toInt).bdiv (2^64) :=
    Int.bmod_eq_self_sub_mul_bdiv _ _
  have h64a : (((2^64 : Nat) : Int) / 2) = (2^63 : Int) := by decide
  have h64b : (((2^64 : Nat) : Int) + 1) / 2 = (2^63 : Int) := by decide
  rw [h64a] at h_bmod_range_lo
  rw [h64b] at h_bmod_range_hi
  rw [h_lift] at h_bdiv_decomp h_bmod_range_lo h_bmod_range_hi
  push_cast at h_bdiv_decomp
  have h_sum_eq :
      q.toInt * (sign_extend (m := 64) y).toInt + s.toInt =
        (sign_extend (m := 64) x).toInt := by
    by_cases hx_nn : 0 ≤ (sign_extend (m := 64) x).toInt
    · have hs_nn := h_s_sign_pos hx_nn
      omega
    · push_neg at hx_nn
      have hs_np := h_s_sign_neg hx_nn
      omega
  obtain ⟨h_tdiv, h_tmod⟩ :=
    int_uniqueness_step_w
      (a := (sign_extend (m := 64) x).toInt)
      (b := (sign_extend (m := 64) y).toInt)
      (q := q.toInt) (r := s.toInt)
      hy_toInt_ne h_sum_eq h_s_sign_pos h_s_sign_neg
      (by simpa [h_s_natAbs] using hbnd_natAbs)
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toInt_eq
    rw [toInt_signExtend32_64, BitVec.toInt_sdiv_of_ne_or_ne x y hne_pair]
    have h_tdiv_xy : x.toInt.tdiv y.toInt = q.toInt := by
      simpa [toInt_signExtend32_64] using h_tdiv
    exact h_tdiv_xy.symm
  · apply BitVec.eq_of_toNat_eq
    rw [bv_abs_toNat_eq_natAbs, toInt_signExtend32_64, BitVec.toInt_srem]
    have h_tmod_xy : x.toInt.tmod y.toInt = s.toInt := by
      simpa [toInt_signExtend32_64] using h_tmod
    rw [h_tmod_xy]
    exact h_s_natAbs.symm

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
  subst sd
  subst sv
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · have hsv_zero : sign_extend (m := 64) y32 = 0#64 := by
      rw [hzero]
      unfold sign_extend Sail.BitVec.signExtend
      decide
    have hq_eq : q = (-1 : BitVec 64) := by
      by_contra hq_ne
      exact h1 ⟨hsv_zero, hq_ne⟩
    have hadj_zero : adj = 0#64 := by
      rw [hadj, hzero]
      exact change_divisor_w_value_of_zero x32
    have hrem_eq : rem = bv_abs (sign_extend (m := 64) x32) := by
      apply rem_from_signfix31_eq_sext32 rem x32
      rw [hq_eq, hadj_zero, BitVec.mul_zero, BitVec.zero_add] at h4
      exact h4
    refine ⟨?_, ?_⟩
    · rw [sail_divw_value_of_zero dividend divisor (by rw [← hy32]; exact hzero),
        hq_eq]
    · have hsail_rem :
          sail_remw_value dividend divisor false = sign_extend (m := 64) x32 := by
        rw [sail_remw_value_of_zero dividend divisor (by rw [← hy32]; exact hzero),
          ← hx32]
      rw [hsail_rem, hrem_eq]
  · by_cases hovf : x32 = BitVec.intMin 32 ∧ y32 = -1#32
    · have hadj_eq : adj = 1#64 := by
        rw [hadj, hovf.1, hovf.2]
        exact change_divisor_w_value_of_overflow
      have habs_one :
          ((1#64 : BitVec 64) ^^^ (1#64 : BitVec 64).sshiftRight 31) -
              (1#64 : BitVec 64).sshiftRight 31 = 1#64 := by
        decide
      have hrem_zero : rem = 0#64 := by
        rcases h5 with h0 | hlt
        · exfalso
          rw [hadj_eq, habs_one] at h0
          exact absurd h0 (by decide)
        · rw [hadj_eq, habs_one] at hlt
          apply bv64_eq_zero_of_toNat_lt_one
          have hOne : ((1#64 : BitVec 64)).toNat = 1 := by decide
          rw [hOne] at hlt
          exact hlt
      have hq_eq : q = sign_extend (m := 64) (BitVec.intMin 32 : BitVec 32) := by
        rw [hadj_eq, hrem_zero] at h4
        have hsigned_zero :
            ((0#64 : BitVec 64) ^^^ (sign_extend (m := 64) x32).sshiftRight 31) -
                (sign_extend (m := 64) x32).sshiftRight 31 = 0#64 := by
          rw [BitVec.zero_xor, BitVec.sub_self]
        rw [hsigned_zero, BitVec.mul_one, BitVec.add_zero] at h4
        rw [h4, hovf.1]
      refine ⟨?_, ?_⟩
      · rw [sail_divw_value_of_overflow dividend divisor
          (by rw [← hx32]; exact hovf.1)
          (by rw [← hy32]; exact hovf.2), hq_eq]
      · rw [sail_remw_value_of_overflow dividend divisor
          (by rw [← hx32]; exact hovf.1)
          (by rw [← hy32]; exact hovf.2), hrem_zero]
        decide
    · have hadj_eq :
          adj = sign_extend (m := 64) y32 := by
        rw [hadj]
        exact change_divisor_w_value_of_normal x32 y32 hovf
      have hbnd : rem.toNat < (bv_abs (sign_extend (m := 64) y32)).toNat := by
        rcases h5 with h0 | hlt
        · exfalso
          rw [hadj_eq, xor_sub_sign31_sext32_eq_bv_abs y32] at h0
          have hpos := bv_abs_sext32_toNat_pos_of_ne_zero y32 hzero
          have hzero_abs : (bv_abs (sign_extend (m := 64) y32)).toNat = 0 := by
            rw [h0]
            rfl
          omega
        · rw [hadj_eq, xor_sub_sign31_sext32_eq_bv_abs y32] at hlt
          exact hlt
      have hprod :
          q * sign_extend (m := 64) y32 +
            ((rem ^^^ (sign_extend (m := 64) x32).sshiftRight 31) -
              (sign_extend (m := 64) x32).sshiftRight 31)
          = sign_extend (m := 64) x32 := by
        rw [hadj_eq] at h4
        exact h4
      obtain ⟨hq, hrem⟩ :=
        advice_unique_normal_w x32 y32 q rem hzero hovf h2 hprod hbnd
      have hne_divisor : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32 := by
        intro h
        apply hzero
        rw [hy32]
        exact h
      have hno_orig :
          ¬ (Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
              Sail.BitVec.extractLsb divisor 31 0 = -1#32) := by
        rintro ⟨hd, hv⟩
        apply hovf
        exact ⟨by rw [hx32, hd], by rw [hy32, hv]⟩
      refine ⟨?_, ?_⟩
      · rw [sail_divw_value_of_normal dividend divisor hne_divisor hno_orig,
          ← hx32, ← hy32, hq]
      · rw [sail_remw_value_of_normal dividend divisor hne_divisor,
          ← hx32, ← hy32, hrem]

end
