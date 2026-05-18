import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `remwProgram`

REMW uses the same signed 32-bit advice guards as DIVW. The architectural
writeback is the signed 32-bit remainder reconstructed from the advised
absolute remainder and the sign of the low 32-bit dividend.
-/

private theorem mod33_toNat_mod32_remw (x : Int) :
    (x % 8589934592).toNat % 4294967296
      = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast_remw (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x
        = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32_remw x

private theorem sail_remw_value_of_zero_remw (dividend divisor : BitVec 64)
    (h : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_remw_value dividend divisor false =
      sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) := by
  unfold sail_remw_value
  simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toInt_zero,
             show ((0 : Int) == 0) = true from rfl]
  rw [trunc32_eq_intCast_remw]
  congr 1
  exact BitVec.ofInt_toInt

private theorem sail_remw_value_of_normal_remw (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32) :
    sail_remw_value dividend divisor false =
      sign_extend (m := 64)
        (BitVec.srem (Sail.BitVec.extractLsb dividend 31 0)
                     (Sail.BitVec.extractLsb divisor 31 0)) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hy32_toInt_ne : y32.toInt ≠ 0 := by
    intro h
    apply hne
    exact BitVec.eq_of_toInt_eq (by simpa using h)
  unfold sail_remw_value
  rw [← hx32, ← hy32]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzero_false : (y32.toInt == (0 : Int)) = false :=
    decide_eq_false hy32_toInt_ne
  simp only [hzero_false]
  rw [trunc32_eq_intCast_remw, ← BitVec.toInt_srem]
  congr 1
  exact BitVec.ofInt_toInt

private lemma extractLsb_signExtend_32_64_remw (x : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0 = x := by
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  bv_decide

private lemma signExtend_extract_signExtend_32_64_remw (x : BitVec 32) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0)
      = sign_extend (m := 64) x := by
  rw [extractLsb_signExtend_32_64_remw]

private lemma sshiftRight31_eq_63_of_sext32_remw (x : BitVec 32) :
    (sign_extend (m := 64) x).sshiftRight 31 =
    (sign_extend (m := 64) x).sshiftRight 63 := by
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma sshiftRight63_signExtend_eq_of_msb_eq_remw (x y : BitVec 32)
    (h : x.msb = y.msb) :
    (sign_extend (m := 64) x).sshiftRight 63 =
    (sign_extend (m := 64) y).sshiftRight 63 := by
  revert h
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

private lemma signfix31_bv_abs_sext32_eq_self_remw (x : BitVec 32) :
    (bv_abs (sign_extend (m := 64) x) ^^^
      (sign_extend (m := 64) x).sshiftRight 31) -
      (sign_extend (m := 64) x).sshiftRight 31 =
    sign_extend (m := 64) x := by
  rw [sshiftRight31_eq_63_of_sext32_remw]
  exact x_eq_bv_abs_xor_sub_sign (sign_extend (m := 64) x)

private theorem sext32_xor_sub_sign_eq_sext32_remw
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
      sshiftRight63_signExtend_eq_of_msb_eq_remw val x32 hmsb_eq
    rw [← hssr_eq]
    exact x_eq_bv_abs_xor_sub_sign (sign_extend (m := 64) val)

private theorem sext32_xor_sub_sign31_eq_sext32_remw
    (val x32 y32 : BitVec 32)
    (hval_srem : val = BitVec.srem x32 y32)
    (hne : y32 ≠ 0#32) :
    (bv_abs (sign_extend (m := 64) val) ^^^
      (sign_extend (m := 64) x32).sshiftRight 31) -
      (sign_extend (m := 64) x32).sshiftRight 31 =
    sign_extend (m := 64) val := by
  rw [sshiftRight31_eq_63_of_sext32_remw]
  exact sext32_xor_sub_sign_eq_sext32_remw val x32 y32 hval_srem hne

/-- Honest `|remainder|`, sign-corrected using the low 32-bit dividend sign,
is exactly Sail's signed REMW result. -/
theorem signed_remw_of_honest_abs_eq_sail_remw (dividend divisor : BitVec 64) :
    let sd := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    ((bv_abs (sail_remw_value dividend divisor false) ^^^ sd.sshiftRight 31) -
        sd.sshiftRight 31) =
      sail_remw_value dividend divisor false := by
  intro sd
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hsd : sd = sign_extend (m := 64) x32 := by
    unfold sd
    rw [← hx32]
  by_cases hzero : y32 = 0#32
  · have hsail :
        sail_remw_value dividend divisor false = sign_extend (m := 64) x32 := by
      rw [sail_remw_value_of_zero_remw dividend divisor (by rw [← hy32]; exact hzero),
        ← hx32]
    rw [hsail, hsd]
    exact signfix31_bv_abs_sext32_eq_self_remw x32
  · have hne_divisor : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32 := by
      intro h
      exact hzero (hy32.trans h)
    have hsail :
        sail_remw_value dividend divisor false =
          sign_extend (m := 64) (BitVec.srem x32 y32) := by
      rw [sail_remw_value_of_normal_remw dividend divisor hne_divisor, ← hx32, ← hy32]
    rw [hsail, hsd]
    exact sext32_xor_sub_sign31_eq_sext32_remw (BitVec.srem x32 y32) x32 y32 rfl hzero

/-- Sail's signed REMW value is already a sign-extended low word. -/
theorem sail_remw_value_sign_extend_roundtrip (dividend divisor : BitVec 64) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sail_remw_value dividend divisor false) 31 0)
      = sail_remw_value dividend divisor false := by
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · have hsail :
        sail_remw_value dividend divisor false =
          sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) := by
      rw [sail_remw_value_of_zero_remw dividend divisor (by rw [← hy32]; exact hzero)]
    rw [hsail, signExtend_extract_signExtend_32_64_remw]
  · have hne_divisor : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32 := by
      intro h
      exact hzero (hy32.trans h)
    have hsail :
        sail_remw_value dividend divisor false =
          sign_extend (m := 64)
            (BitVec.srem (Sail.BitVec.extractLsb dividend 31 0)
                         (Sail.BitVec.extractLsb divisor 31 0)) := by
      rw [sail_remw_value_of_normal_remw dividend divisor hne_divisor]
    rw [hsail, signExtend_extract_signExtend_32_64_remw]

end
