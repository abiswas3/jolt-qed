import Mathlib.Data.Nat.Bitwise
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Bridges for shift instructions

Pure `BitVec` math connecting the Jolt bitmask / multiply-by-power-of-two
encodings of shifts to their direct Sail counterparts. Split into three
groups, one per shift direction:

* `sllw_mul_eq_shift` — SLLW: multiply by `2 ^ s` equals left shift by `s`
* `srlw_shift_eq` — SRLW: `shl 32 then shr (s+32)` via bitmask encoding
  equals 32-bit logical right shift
* `sraw_five_step_value` — SRAW: sign-extend + bitmask arithmetic shift
  equals 32-bit arithmetic right shift

-/

-- ============================================================================
-- SLLW bridge
-- ============================================================================

/-- From `BytecodeExpansions/Instructions/Sllw.lean`. -/
def sllwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_pow := Jolt.virtualPow2W rs2_val
  let product := Riscv.mul rs1_val v_pow
  Jolt.virtualSignExtendWord product

private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]

theorem sllw_eq_sllwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sllw rs1_val rs2_val = sllwJolt rs1_val rs2_val := by
  unfold Riscv.sllw sllwJolt Jolt.virtualPow2W Riscv.mul Jolt.virtualSignExtendWord
  congr 1
  exact sll_32_eq_mul_trunc rs1_val (rs2_val.setWidth 5).toNat (by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this)

private lemma mul_eq_sllwJolt (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sllwJolt v1 v2 := by
  unfold sllwJolt Jolt.virtualSignExtendWord Jolt.virtualPow2W Riscv.mul sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]

private lemma sail_sllw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sllw v1 v2 := by
  unfold Riscv.sllw sign_extend shift_bits_left
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

/-- Bridge: the MUL-based Jolt SLLW computation equals Sail's native SLLW. -/
theorem sllw_mul_eq_shift (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [mul_eq_sllwJolt, sail_sllw_eq_riscv, sllw_eq_sllwJolt]

-- ============================================================================
-- SRLW bridge
-- ============================================================================

/-- From `BytecodeExpansions/Instructions/Srlw.lean`. -/
def srlw_bitmask (rs2_val : BitVec 64) : Nat :=
  let v_bitmask_in := Riscv.ori rs2_val 32#64
  let shift := (v_bitmask_in.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

private lemma or32_setWidth6_toNat (x : BitVec 64) :
    ((Riscv.ori x 32#64).setWidth 6).toNat = (x.setWidth 5).toNat + 32 := by
  have h : (Riscv.ori x 32#64).setWidth 6 = ((1#1) +++ x.setWidth 5) := by
    unfold Riscv.ori
    bv_decide
  rw [h, BitVec.toNat_append]
  norm_num [Nat.shiftLeft_eq]
  change (2 ^ 5 ||| (x.setWidth 5).toNat) = (x.setWidth 5).toNat + 32
  rw [show (x.setWidth 5).toNat + 32 = 2 ^ 5 + (x.setWidth 5).toNat by
    norm_num
    omega]
  have hx : (x.setWidth 5).toNat < 2 ^ 5 := by
    have := (x.setWidth 5).isLt
    norm_num at this
    exact this
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  by_cases hi5 : i = 5
  · subst i
    rw [Nat.testBit_two_pow_self, Nat.testBit_two_pow_add_eq]
    have hk : (x.setWidth 5).toNat.testBit 5 = false := Nat.testBit_lt_two_pow hx
    simpa [BitVec.toNat_setWidth] using hk
  · by_cases hlt : i < 5
    · have hpow : (2 ^ 5 : Nat).testBit i = false := by
        rw [Nat.testBit_two_pow]
        simp [show ¬5 = i by omega]
      rw [hpow, Bool.false_or, Nat.testBit_two_pow_add_gt hlt]
    · have hgt : 5 < i := by omega
      have hk : (x.setWidth 5).toNat.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)))
      have hpow : (2 ^ 5 : Nat).testBit i = false := by
        rw [Nat.testBit_two_pow]
        simp [show ¬5 = i by omega]
      have hadd : (2 ^ 5 + (x.setWidth 5).toNat).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have hb : 2 ^ 5 + (x.setWidth 5).toNat < 2 ^ 6 := by omega
        exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
      rw [hpow, hk, hadd]
      rfl

lemma ctz_srlw_bitmask (rs2_val : BitVec 64) :
    ctz (srlw_bitmask rs2_val) = (rs2_val.setWidth 5).toNat + 32 := by
  unfold srlw_bitmask
  simp only [or32_setWidth6_toNat]
  simp only [Nat.shiftLeft_eq, one_mul]
  have h_lt : (rs2_val.setWidth 5).toNat < 32 := by
    have := (rs2_val.setWidth 5).isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - ((rs2_val.setWidth 5).toNat + 32) := by omega
  have h_m_pos : 0 < 2 ^ (64 - ((rs2_val.setWidth 5).toNat + 32)) - 1 := by
    have : 2 ≤ 2 ^ (64 - ((rs2_val.setWidth 5).toNat + 32)) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 ((rs2_val.setWidth 5).toNat + 32) h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]

private lemma toNat_shl_32 (v : BitVec 64) :
    (v <<< 32).toNat = v.toNat * 2^32 % 2^64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private lemma mul_mod_div_cancel (a s : Nat) (hs : s < 32) :
    a * 2^32 % 2^64 / 2^(s + 32) = a % 2^32 / 2^s := by
  have h1 : a * 2^32 % 2^64 = a % 2^32 * 2^32 := by omega
  have h2 : (2:Nat)^(s + 32) = 2^s * 2^32 := by
    have : (2:Nat)^32 = 2^32 := rfl
    rw [Nat.pow_add]
  rw [h1, h2, Nat.mul_div_mul_right _ _ (by positivity : (0:Nat) < 2^32)]

private lemma nat_shr_zero (n : Nat) : n >>> 0 = n := by simp

private lemma shl_shr_setWidth (v1 v2 : BitVec 64)
    (hs : (v2.setWidth 5).toNat < 32) :
    BitVec.extractLsb' 0 32 (v1 <<< 32 >>> ((v2.setWidth 5).toNat + 32)) =
    BitVec.extractLsb' 0 32 v1 >>> BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 v2) := by
  unfold BitVec.extractLsb'
  simp only [nat_shr_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             Nat.reducePow]
  rw [toNat_shl_32 v1, mul_mod_div_cancel v1.toNat _ hs]
  simp only [Nat.reducePow]
  have hbound : v1.toNat % 4294967296 / 2 ^ (BitVec.setWidth 5 v2).toNat < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
  rw [Nat.mod_eq_of_lt hbound]
  change _ = (BitVec.ofNat 32 v1.toNat >>> (BitVec.ofNat 5 (v2.toNat % 4294967296)).toNat).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have : v2.toNat % 4294967296 % 32 = (BitVec.setWidth 5 v2).toNat := by
    simp [BitVec.toNat_setWidth]
  rw [this]

/-- Bridge: the SLLI+bitmask+VirtualSRL Jolt SRLW computation equals
Sail's native SRLW. -/
theorem srlw_shift_eq (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [show ctz (srlw_bitmask v2) = (v2.setWidth 5).toNat + 32 from ctz_srlw_bitmask v2]
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend,
             Sail.BitVec.extractLsb, BitVec.extractLsb,
             Nat.sub_zero, Nat.reduceAdd]
  congr 1
  have hs : (v2.setWidth 5).toNat < 32 := by
    have := (v2.setWidth 5).isLt; norm_num at this; exact this
  exact shl_shr_setWidth v1 v2 hs

-- ============================================================================
-- SRAW bridge
-- ============================================================================

/-- From `BytecodeExpansions/Instructions/Sraw.lean`. -/
def sraw_bitmask (shamt_val : BitVec 64) : Nat :=
  let shift := (shamt_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_sraw_bitmask (shamt_val : BitVec 64) :
    ctz (sraw_bitmask shamt_val) = (shamt_val.setWidth 6).toNat := by
  unfold sraw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt_val.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (shamt_val.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private lemma ctz_sraw_chain (rs2_val : BitVec 64) :
    ctz (sraw_bitmask (Riscv.andi rs2_val 0x1f#64)) = (rs2_val.setWidth 5).toNat := by
  rw [ctz_sraw_bitmask]
  unfold Riscv.andi
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : (31 : Nat) % 2 ^ 64 = 31 := by norm_num
  rw [h1, show (31 : Nat) = 2 ^ 5 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt rs2_val.toNat (show 0 < 2 ^ 5 from by positivity); omega)

def srawJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_rs1     := Jolt.virtualSignExtendWord rs1_val
  let v_shamt   := Riscv.andi rs2_val 0x1f#64
  let v_bitmask := sraw_bitmask v_shamt
  let v_result  := v_rs1 >>> ctz v_bitmask
  Jolt.virtualSignExtendWord v_result

theorem sraw_eq_srawJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sraw rs1_val rs2_val = srawJolt rs1_val rs2_val := by
  unfold Riscv.sraw srawJolt Jolt.virtualSignExtendWord
  simp only [ctz_sraw_chain]
  have hs : (rs2_val.setWidth 5).toNat < 32 := by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this
  congr 1
  rw [sshiftRight_eq_signExtend_ushr_trunc (rs1_val.setWidth 32) _ hs]

private lemma five_step_eq_srawJolt (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>>
          ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0) =
    srawJolt v1 v2 := by
  unfold srawJolt Jolt.virtualSignExtendWord sign_extend Riscv.andi
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 2

private lemma sail_sraw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sraw v1 v2 := by
  unfold Riscv.sraw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']
  congr 2

/-- Bridge: the 5-step Jolt SRAW computation (sign-extend, mask, shift
via bitmask, sign-extend) equals Sail's native SRAW. -/
theorem sraw_five_step_value (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>>
          ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [five_step_eq_srawJolt, sail_sraw_eq_riscv, sraw_eq_srawJolt]

end
