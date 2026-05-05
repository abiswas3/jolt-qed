import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULHSU: Rust inline sequence = Sail MULHSU

This file models the RV64 `tracer/src/instruction/mulhsu.rs` inline sequence
literally:

```
VirtualMovsign v0, rs1
ANDI           v1, v0, 1
XOR            v2, rs1, v0
ADD            v2, v2, v1
MULHU          v3, v2, rs2
MUL            v2, v2, rs2
XOR            v3, v3, v0
XOR            v2, v2, v0
ADD            v0, v2, v1
SLTU           v0, v0, v2
ADD            rd, v3, v0
```
-/

def mulhsuOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Unsigned }

/-- Upper 64 bits of a signed-by-unsigned 64x64 multiply. -/
def mulhsu (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * (b.toNat : Int)) / (2 ^ 64))

/-- Auxiliary arithmetic form used to relate the Rust sequence to RV64 `MULHSU`. -/
def jolt_mulhsu_correction_value (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y

/-- The pure value written by the Rust `MULHSU` inline sequence. -/
def jolt_mulhsu_value (x y : BitVec 64) : BitVec 64 :=
  let sx := jolt_movsign_value x
  let one := sx &&& sign_extend (m := 64) (1#12 : BitVec 12)
  let absx := (x ^^^ sx) + one
  let hi := jolt_mulhu_value absx y
  let lo := absx * y
  let hiNeg := hi ^^^ sx
  let loNeg := lo ^^^ sx
  hiNeg + jolt_sltu_value (loNeg + one) loNeg

/-- Rust's RV64 `MULHSU::inline_sequence`, with allocator outputs fixed as
`v0 = 0`, `v1 = 1`, `v2 = 2`, `v3 = 3`. -/
def jolt_mulhsu (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_movsign_from_real 0 rs1
  let _ ← vreg_ANDI 1 0 1
  let _ ← vreg_XOR_from_real_vs1 2 rs1 0
  let _ ← vreg_ADD 2 2 1
  let _ ← vreg_MULHU_from_real_vs2 3 2 rs2
  let _ ← vreg_MUL_from_real_vs2 2 2 rs2
  let _ ← vreg_XOR 3 3 0
  let _ ← vreg_XOR 2 2 0
  let _ ← vreg_ADD 0 2 1
  let _ ← vreg_SLTU 0 0 2
  vreg_ADD_to_real rd 3 0

private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    to_bits_truncate, Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega

private theorem mulhsu_eq_sail_mulhsu_value (v1 v2 : BitVec 64) :
    mulhsu v1 v2 =
      mult_to_bits_half (l := LeanRV64D.Functions.xlen)
        Signedness.Signed Signedness.Unsigned v1 v2 VectorHalf.High := by
  unfold mulhsu mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.ofInt 64 (v1.toInt * (v2.toNat : Int) / 2^64) =
    BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (v1.toInt * (v2.toNat : Int))) 127 64)
  rw [extract_high64_to_bits_truncate_eq_ofInt_div]
  simp

private theorem toInt_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt]
  have hcond : 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]

private theorem toInt_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    x.toInt = (x.toNat : Int) - (18446744073709551616 : Int) := by
  rw [BitVec.toInt]
  have hcond : ¬ 2 * x.toNat < 18446744073709551616 := by omega
  simp only [Nat.reducePow, hcond, ↓reduceIte]
  norm_num

private theorem xor_neg_one_toNat (x : BitVec 64) :
    (x ^^^ (-1 : BitVec 64)).toNat =
      18446744073709551616 - 1 - x.toNat := by
  rw [show x ^^^ (-1 : BitVec 64) = ~~~x by bv_decide]
  rw [BitVec.toNat_not]

private theorem abs_neg_toNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1).toNat =
      18446744073709551616 - x.toNat := by
  rw [BitVec.toNat_add, xor_neg_one_toNat]
  have hxpos : 0 < x.toNat := by omega
  rw [show (1 : BitVec 64).toNat = 1 by decide]
  norm_num
  omega

private theorem abs_neg_eq_ofNat (x : BitVec 64)
    (hx : ¬ x.toNat < 9223372036854775808) :
    ((x ^^^ (-1 : BitVec 64)) + 1) =
      BitVec.ofNat 64 (18446744073709551616 - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [abs_neg_toNat x hx, BitVec.toNat_ofNat]
  have hxpos : 0 < x.toNat := by omega
  norm_num
  omega

private theorem mulhsu_corr_neg_arith (a b : Nat) :
    (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 =
      ((((a : Int) - 18446744073709551616) * (b : Int) /
            18446744073709551616) % 18446744073709551616).toNat := by
  rw [show ((a : Int) - 18446744073709551616) * (b : Int) =
      ((a * b : Nat) : Int) - 18446744073709551616 * (b : Int) by
    rw [Nat.cast_mul]
    ring]
  omega

private theorem div_complement_mod_zero (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  omega

private theorem div_complement_mod_pos (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hr : ¬ (18446744073709551616 - a) * b %
        18446744073709551616 = 0) :
    a * b / 18446744073709551616 =
      b - ((18446744073709551616 - a) * b /
        18446744073709551616) - 1 := by
  have ha_le : a ≤ 18446744073709551616 := by omega
  have hmul : a * b + (18446744073709551616 - a) * b =
      18446744073709551616 * b := by
    have ha_sum : a + (18446744073709551616 - a) =
        18446744073709551616 := Nat.add_sub_of_le ha_le
    nlinarith [Nat.left_distrib b a (18446744073709551616 - a)]
  have hdiv := Nat.div_add_mod ((18446744073709551616 - a) * b)
    18446744073709551616
  have hrpos : 0 < (18446744073709551616 - a) * b %
      18446744073709551616 := by omega
  have hrlt : (18446744073709551616 - a) * b %
      18446744073709551616 < 18446744073709551616 :=
    Nat.mod_lt _ (by norm_num)
  omega

private theorem neg_high_mod_zero (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q ≤ b) :
    (18446744073709551616 - q) % 18446744073709551616 =
      (b - q + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.sub_zero]
    rw [show b + 18446744073709551615 * b =
        18446744073709551616 * b by omega]
    rw [Nat.mul_mod_right]
  · have hqpos : 0 < q := by omega
    have hbpos : 0 < b := by omega
    have hqN : q < 18446744073709551616 := by omega
    have hleft : (18446744073709551616 - q) %
        18446744073709551616 = 18446744073709551616 - q := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hleft]
    have hright_eq :
        b - q + 18446744073709551615 * b =
          18446744073709551616 * (b - 1) +
            (18446744073709551616 - q) := by
      omega
    rw [hright_eq]
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp
    exact hleft.symm

private theorem neg_high_mod_pos (b q : Nat)
    (hb : b < 18446744073709551616) (hq : q + 1 ≤ b) :
    (18446744073709551616 - 1 - q) % 18446744073709551616 =
      (b - q - 1 + 18446744073709551615 * b) %
        18446744073709551616 := by
  have hbpos : 0 < b := by omega
  have hqN : q < 18446744073709551616 := by omega
  have hleft : (18446744073709551616 - 1 - q) %
      18446744073709551616 = 18446744073709551616 - 1 - q := by
    apply Nat.mod_eq_of_lt
    omega
  rw [hleft]
  have hright_eq :
      b - q - 1 + 18446744073709551615 * b =
        18446744073709551616 * (b - 1) +
          (18446744073709551616 - 1 - q) := by
    omega
  rw [hright_eq]
  rw [Nat.add_mod, Nat.mul_mod_right]
  simp
  exact hleft.symm

private theorem neg_high_eq_mulhsu_correction (a b : Nat)
    (ha : ¬ a < 9223372036854775808)
    (haN : a < 18446744073709551616)
    (hbN : b < 18446744073709551616) :
    (18446744073709551615 -
          ((18446744073709551616 - a) * b /
            18446744073709551616) +
        (if ((18446744073709551615 -
                ((18446744073709551616 - a) * b %
                  18446744073709551616) + 1) %
              18446744073709551616) <
            18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616)
          then 1 else 0)) % 18446744073709551616 =
      (a * b / 18446744073709551616 + 18446744073709551615 * b) %
        18446744073709551616 := by
  by_cases hr : (18446744073709551616 - a) * b %
      18446744073709551616 = 0
  · rw [div_complement_mod_zero a b ha haN hr]
    simp [hr]
    have hq_le : (18446744073709551616 - a) * b /
        18446744073709551616 ≤ b := by
      apply Nat.div_le_of_le_mul
      have hm : 18446744073709551616 - a ≤ 18446744073709551616 :=
        Nat.sub_le _ _
      nlinarith
    rw [show 18446744073709551615 -
        ((18446744073709551616 - a) * b / 18446744073709551616) + 1 =
          18446744073709551616 -
            ((18446744073709551616 - a) * b /
              18446744073709551616) by omega]
    exact neg_high_mod_zero b
      ((18446744073709551616 - a) * b / 18446744073709551616)
      hbN hq_le
  · have hcond : ¬
        ((18446744073709551615 -
              ((18446744073709551616 - a) * b %
                18446744073709551616) + 1) %
            18446744073709551616) <
          18446744073709551615 -
            ((18446744073709551616 - a) * b %
              18446744073709551616) := by
      have hrpos : 0 < (18446744073709551616 - a) * b %
          18446744073709551616 := by omega
      have hrlt : (18446744073709551616 - a) * b %
          18446744073709551616 < 18446744073709551616 :=
        Nat.mod_lt _ (by norm_num)
      rw [show 18446744073709551615 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) + 1 =
        18446744073709551616 -
          ((18446744073709551616 - a) * b %
            18446744073709551616) by omega]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [div_complement_mod_pos a b ha haN hr]
    simp [hcond]
    apply neg_high_mod_pos
    · exact hbN
    · have hbpos : 0 < b := by
        by_contra hb
        have hb0 : b = 0 := by omega
        simp [hb0] at hr
      have hm_lt : 18446744073709551616 - a <
          18446744073709551616 := by omega
      have hdivlt : (18446744073709551616 - a) * b /
          18446744073709551616 < b := by
        rw [Nat.div_lt_iff_lt_mul
          (by norm_num : 0 < 18446744073709551616)]
        nlinarith
      omega

private theorem jolt_mulhsu_value_eq_correction (x y : BitVec 64) :
    jolt_mulhsu_value x y = jolt_mulhsu_correction_value x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value
    rw [jolt_sltu_value_eq_zero_of_not_lt]
    · apply BitVec.eq_of_toNat_eq
      simp
    · simp
  · rw [jolt_mulhsu_value, jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    change (jolt_mulhu_value
          ((x ^^^ (-1 : BitVec 64)) +
            ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12))) y ^^^ (-1 : BitVec 64)) +
        jolt_sltu_value (((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) + 1)
          ((((x ^^^ (-1 : BitVec 64)) + 1) * y) ^^^ (-1 : BitVec 64)) =
      jolt_mulhu_value x y + (-1 : BitVec 64) * y
    rw [show ((-1 : BitVec 64) &&& sign_extend (m := 64) (1#12 : BitVec 12)) =
      1 by decide]
    rw [abs_neg_eq_ofNat x hx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      (jolt_mulhu_value (BitVec.ofNat 64 (18446744073709551616 - x.toNat)) y)]
    rw [jolt_sltu_value_toNat]
    rw [BitVec.toNat_add]
    rw [xor_neg_one_toNat
      ((BitVec.ofNat 64 (18446744073709551616 - x.toNat)) * y)]
    unfold jolt_mulhu_value
    rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofNat, BitVec.toNat_mul]
    rw [show (1 : BitVec 64).toNat = 1 by decide]
    rw [show (-1 : BitVec 64).toNat = 18446744073709551615 by decide]
    norm_num
    have hNx : (18446744073709551616 - x.toNat) %
        18446744073709551616 = 18446744073709551616 - x.toNat := by
      apply Nat.mod_eq_of_lt
      have hxpos : 0 < x.toNat := by omega
      omega
    rw [hNx]
    have hq1 : (18446744073709551616 - x.toNat) * y.toNat /
        18446744073709551616 < 18446744073709551616 := by
      rw [Nat.div_lt_iff_lt_mul
        (by norm_num : 0 < 18446744073709551616)]
      have hxpos : 0 < x.toNat := by omega
      have hm_lt : 18446744073709551616 - x.toNat <
          18446744073709551616 := by omega
      nlinarith [hm_lt, y.isLt]
    rw [Nat.mod_eq_of_lt hq1]
    exact neg_high_eq_mulhsu_correction x.toNat y.toNat hx x.isLt y.isLt

private theorem jolt_mulhsu_correction_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_correction_value x y = mulhsu x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_zero_of_toNat_lt_half x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_toNat_lt_half x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  · rw [jolt_mulhsu_correction_value,
      jolt_movsign_value_eq_neg_one_of_half_le x hx]
    unfold jolt_mulhu_value mulhsu
    rw [toInt_of_half_le x hx]
    apply BitVec.eq_of_toNat_eq
    simp
    exact mulhsu_corr_neg_arith x.toNat y.toNat

private theorem jolt_mulhsu_value_eq_mulhsu (x y : BitVec 64) :
    jolt_mulhsu_value x y = mulhsu x y := by
  rw [jolt_mulhsu_value_eq_correction, jolt_mulhsu_correction_eq_mulhsu]

theorem execute_MULHSU_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhsuOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhsu v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhsuOp, mulhsu_eq_sail_mulhsu_value, bind_pure_comp]

theorem jolt_mulhsu_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (jsf : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulhsu rs2 rs1 rd).run js = .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhsu v1 v2) := by
  unfold jolt_mulhsu vreg_movsign_from_real vreg_ANDI vreg_XOR_from_real_vs1
    vreg_ADD vreg_MULHU_from_real_vs2 vreg_MUL_from_real_vs2 vreg_XOR
    vreg_SLTU vreg_ADD_to_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    readVReg, writeVReg, get, modify, modifyGet, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet]
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  simp only [h1, h2]
  simp
  let out := jolt_mulhsu_value v1 v2
  obtain ⟨sf, hw⟩ := wX_shape rd out js.sail
  rw [show wX_bits rd
      ((jolt_mulhu_value
          ((v1 ^^^ jolt_movsign_value v1) +
            (jolt_movsign_value v1 &&& sign_extend (m := 64) (1#12 : BitVec 12))) v2 ^^^
          jolt_movsign_value v1) +
        jolt_sltu_value
          ((((v1 ^^^ jolt_movsign_value v1) +
                (jolt_movsign_value v1 &&& sign_extend (m := 64) (1#12 : BitVec 12))) * v2 ^^^
              jolt_movsign_value v1) +
            (jolt_movsign_value v1 &&& sign_extend (m := 64) (1#12 : BitVec 12)))
          (((v1 ^^^ jolt_movsign_value v1) +
              (jolt_movsign_value v1 &&& sign_extend (m := 64) (1#12 : BitVec 12))) * v2 ^^^
            jolt_movsign_value v1)) js.sail = .ok () sf by
    simpa [out, jolt_mulhsu_value] using hw]
  simp only
  refine ⟨_, rfl, ?_⟩
  change sf = stateAfterWrite js.sail rd (mulhsu v1 v2)
  rw [wX_bits_eq_stateAfterWrite rd out js.sail sf hw]
  change stateAfterWrite js.sail rd (jolt_mulhsu_value v1 v2) =
    stateAfterWrite js.sail rd (mulhsu v1 v2)
  rw [jolt_mulhsu_value_eq_mulhsu]

theorem jolt_mulhsu_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulhsu rs2 rs1 rd).run js) =
    (execute_MUL rs2 rs1 rd mulhsuOp).run js.sail :=
  rtype_eq_sail_uniform
    (f := mulhsu)
    (execute_MULHSU_factored rs2 rs1 rd)
    (jolt_mulhsu_concrete rs2 rs1 rd hrd js hwf)

end
