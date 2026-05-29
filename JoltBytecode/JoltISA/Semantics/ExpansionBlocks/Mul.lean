import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions
import Mathlib

/-!
# M-extension expansion block semantics

These lemmas describe source-instruction inline blocks after they have been
lowered to real Jolt ISA rows.  In particular, nested `MULH` expansions must
use the scratch virtual registers allocated at the call site.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true
set_option linter.unusedVariables false

noncomputable section

namespace JoltISA

/-- Pure value computed by the lowered `MULH` block. -/
def mulhBlockValue (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y + jolt_movsign_value y * x

/-- Extracting bits 127 down to 64 from a 128-bit truncated integer is the same
as dividing that integer by `2^64` and keeping the low 64 bits. -/
private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', to_bits_truncate,
        Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega

/-- A 64-bit word below `2^63` has signed interpretation equal to its unsigned
natural-number value. -/
private theorem toInt_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt]
  have hcond : 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]

/-- A 64-bit word at least `2^63` has signed interpretation equal to its
unsigned value minus `2^64`. -/
private theorem toInt_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) - (18446744073709551616 : Int) := by
  rw [BitVec.toInt]
  have hcond : ¬ 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
  norm_num

/-- Arithmetic correction for the case where `rs1` is negative and `rs2` is
nonnegative. -/
private theorem mulh_corr_neg_pos_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 =
      ((((a : Int) - 18446744073709551616) * (b : Int) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) * (b : Int) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) by
    rw [Nat.cast_mul]
    ring]
  omega

/-- Arithmetic correction for the case where `rs1` is nonnegative and `rs2` is
negative. -/
private theorem mulh_corr_pos_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * a) %
        18446744073709551616 =
      (((a : Int) * ((b : Int) - 18446744073709551616) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show (a : Int) * ((b : Int) - 18446744073709551616) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (a : Int) by
    rw [Nat.cast_mul]
    ring]
  omega

/-- Arithmetic correction for the case where both operands are negative. -/
private theorem mulh_corr_neg_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b +
        18446744073709551615 * a) % 18446744073709551616 =
      ((((a : Int) - 18446744073709551616) *
          ((b : Int) - 18446744073709551616) / 18446744073709551616) %
        18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) *
        ((b : Int) - 18446744073709551616) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) -
        18446744073709551616 * (a : Int) +
          18446744073709551616 * 18446744073709551616 by
    rw [Nat.cast_mul]
    ring]
  omega

/-- The `MULH` block's unsigned-high product plus the two sign corrections is
exactly the signed-high product required by RV64 `MULH`. -/
theorem mulhBlockValue_eq_mulhs (x y : BitVec 64) :
    mulhBlockValue x y = mulhs x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [mulhBlockValue, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      omega
    · rw [mulhBlockValue, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_pos_neg_arith x.toNat y.toNat
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [mulhBlockValue, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_half_le x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_pos_arith x.toNat y.toNat
    · rw [mulhBlockValue, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_half_le x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_neg_arith x.toNat y.toNat

/-- The lowered `MULH v3, v0, v2` block used by DIV/REM writes the signed-high
product to `v3`, preserves the advice/divisor registers `v0`, `v1`, `v2`, and
runs any continuation from that checkpoint.  The scratch registers `v4`, `v5`,
and `v6` are the allocator outputs Rust consumes inside the nested `MULH`. -/
theorem exists_state_after_div_rem_mulh_block_run
    (js : SailJoltState) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs 0 = js.vregs 0 ∧
      js'.vregs 1 = js.vregs 1 ∧
      js'.vregs 2 = js.vregs 2 ∧
      js'.vregs 3 = mulhs (js.vregs 0) (js.vregs 2) ∧
      ∀ tail,
        (execProgram (mulhBlock 4 5 6 (.vreg 3) (.vreg 0) (.vreg 2) tail)).run js =
          (execProgram tail).run js' := by
  let lhs := js.vregs (0 : VReg)
  let rhs := js.vregs (2 : VReg)
  let lhsSign := jolt_movsign_value lhs
  let rhsSign := jolt_movsign_value rhs
  let lhsCorrection := lhsSign * rhs
  let rhsCorrection := rhsSign * lhs
  let unsignedHigh := jolt_mulhu_value lhs rhs
  let highWithLhsCorrection := unsignedHigh + lhsCorrection

  -- Block row 1: `VirtualMovsign v4, v0`.
  obtain ⟨s1, h1_sail, h1_v4, h1_pres, h1_succeeds⟩ :=
    exists_state_after_movsign_run_vreg_vreg
      (4 : VReg) (0 : VReg) js lhs rfl

  -- Block row 2: `VirtualMovsign v5, v2`.
  have h1_v2 : s1.vregs (2 : VReg) = rhs :=
    (h1_pres (2 : VReg) (by decide)).trans rfl
  obtain ⟨s2, h2_sail, h2_v5, h2_pres, h2_succeeds⟩ :=
    exists_state_after_movsign_run_vreg_vreg
      (5 : VReg) (2 : VReg) s1 rhs h1_v2

  -- Block row 3: `MUL v4, v4, v2`.
  have h2_v4 : s2.vregs (4 : VReg) = lhsSign :=
    (h2_pres (4 : VReg) (by decide)).trans h1_v4
  have h2_v2 : s2.vregs (2 : VReg) = rhs :=
    (h2_pres (2 : VReg) (by decide)).trans h1_v2
  obtain ⟨s3, h3_sail, h3_v4, h3_pres, h3_succeeds⟩ :=
    exists_state_after_mul_run_vreg_vreg_vreg
      (4 : VReg) (4 : VReg) (2 : VReg) s2 lhsSign rhs h2_v4 h2_v2

  -- Block row 4: `MUL v5, v5, v0`.
  have h3_v5 : s3.vregs (5 : VReg) = rhsSign :=
    (h3_pres (5 : VReg) (by decide)).trans h2_v5
  have h3_v0 : s3.vregs (0 : VReg) = lhs :=
    (h3_pres (0 : VReg) (by decide)).trans
      ((h2_pres (0 : VReg) (by decide)).trans (h1_pres (0 : VReg) (by decide)))
  obtain ⟨s4, h4_sail, h4_v5, h4_pres, h4_succeeds⟩ :=
    exists_state_after_mul_run_vreg_vreg_vreg
      (5 : VReg) (5 : VReg) (0 : VReg) s3 rhsSign lhs h3_v5 h3_v0

  -- Block row 5: `MULHU v6, v0, v2`.
  have h4_v0 : s4.vregs (0 : VReg) = lhs :=
    (h4_pres (0 : VReg) (by decide)).trans h3_v0
  have h4_v2 : s4.vregs (2 : VReg) = rhs :=
    (h4_pres (2 : VReg) (by decide)).trans
      ((h3_pres (2 : VReg) (by decide)).trans h2_v2)
  obtain ⟨s5, h5_sail, h5_v6, h5_pres, h5_succeeds⟩ :=
    exists_state_after_mulhu_run_vreg_vreg_vreg
      (6 : VReg) (0 : VReg) (2 : VReg) s4 lhs rhs h4_v0 h4_v2

  -- Block row 6: `ADD v6, v6, v4`.
  have h5_v4 : s5.vregs (4 : VReg) = lhsCorrection :=
    (h5_pres (4 : VReg) (by decide)).trans
      ((h4_pres (4 : VReg) (by decide)).trans h3_v4)
  obtain ⟨s6, h6_sail, h6_v6, h6_pres, h6_succeeds⟩ :=
    exists_state_after_add_run_vreg_vreg_vreg
      (6 : VReg) (6 : VReg) (4 : VReg) s5 unsignedHigh lhsCorrection
      h5_v6 h5_v4

  -- Block row 7: `ADD v3, v6, v5`.
  have h6_v5 : s6.vregs (5 : VReg) = rhsCorrection :=
    (h6_pres (5 : VReg) (by decide)).trans
      ((h5_pres (5 : VReg) (by decide)).trans h4_v5)
  obtain ⟨s7, h7_sail, h7_v3, h7_pres, h7_succeeds⟩ :=
    exists_state_after_add_run_vreg_vreg_vreg
      (3 : VReg) (6 : VReg) (5 : VReg) s6 highWithLhsCorrection rhsCorrection
      h6_v6 h6_v5

  have h7_sail_orig : s7.sail = js.sail :=
    h7_sail.trans (h6_sail.trans (h5_sail.trans (h4_sail.trans
      (h3_sail.trans (h2_sail.trans h1_sail)))))
  have h7_v0 : s7.vregs (0 : VReg) = js.vregs (0 : VReg) :=
    (h7_pres (0 : VReg) (by decide)).trans
      ((h6_pres (0 : VReg) (by decide)).trans
        ((h5_pres (0 : VReg) (by decide)).trans
          ((h4_pres (0 : VReg) (by decide)).trans h3_v0)))
  have h7_v1 : s7.vregs (1 : VReg) = js.vregs (1 : VReg) :=
    (h7_pres (1 : VReg) (by decide)).trans
      ((h6_pres (1 : VReg) (by decide)).trans
        ((h5_pres (1 : VReg) (by decide)).trans
          ((h4_pres (1 : VReg) (by decide)).trans
            ((h3_pres (1 : VReg) (by decide)).trans
              ((h2_pres (1 : VReg) (by decide)).trans
                (h1_pres (1 : VReg) (by decide)))))))
  have h7_v2 : s7.vregs (2 : VReg) = js.vregs (2 : VReg) :=
    (h7_pres (2 : VReg) (by decide)).trans
      ((h6_pres (2 : VReg) (by decide)).trans
        ((h5_pres (2 : VReg) (by decide)).trans h4_v2))
  have h7_v3_mulhs : s7.vregs (3 : VReg) = mulhs (js.vregs 0) (js.vregs 2) := by
    rw [h7_v3]
    change mulhBlockValue lhs rhs = mulhs lhs rhs
    exact mulhBlockValue_eq_mulhs lhs rhs

  refine ⟨s7, h7_sail_orig, h7_v0, h7_v1, h7_v2, h7_v3_mulhs, ?_⟩
  intro tail
  unfold mulhBlock
  rw [execProgram_instr_run_retire _ _ js s1 h1_succeeds]
  rw [execProgram_instr_run_retire _ _ s1 s2 h2_succeeds]
  rw [execProgram_instr_run_retire _ _ s2 s3 h3_succeeds]
  rw [execProgram_instr_run_retire _ _ s3 s4 h4_succeeds]
  rw [execProgram_instr_run_retire _ _ s4 s5 h5_succeeds]
  rw [execProgram_instr_run_retire _ _ s5 s6 h6_succeeds]
  rw [execProgram_instr_run_retire _ _ s6 s7 h7_succeeds]

end JoltISA

end
