import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULH: Rust inline sequence = Sail MULH

This file models the RV64 `tracer/src/instruction/mulh.rs` inline sequence
literally:

```
VirtualMovsign v_sx, rs1
VirtualMovsign v_sy, rs2
MUL            v_sx, v_sx, rs2
MUL            v_sy, v_sy, rs1
MULHU          v_tmp, rs1, rs2
ADD            v_tmp, v_tmp, v_sx
ADD            rd,    v_tmp, v_sy
```

The Jolt-ISA virtual instructions used here live in `VirtualInstructions.lean`.
-/

def mulhOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

/-- The pure value written by the Rust `MULH` inline sequence. -/
def jolt_mulh_value (x y : BitVec 64) : BitVec 64 :=
  jolt_mulhu_value x y + jolt_movsign_value x * y + jolt_movsign_value y * x

/-- Rust's RV64 `MULH::inline_sequence`, with allocator outputs fixed as
`v_sx = 0`, `v_sy = 1`, `v_tmp = 2`. -/
def jolt_mulh (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_movsign_from_real 0 rs1
  let _ ← vreg_movsign_from_real 1 rs2
  let _ ← vreg_MUL_from_real_vs2 0 0 rs2
  let _ ← vreg_MUL_from_real_vs2 1 1 rs1
  let _ ← vreg_MULHU_from_real 2 rs1 rs2
  let _ ← vreg_ADD 2 2 0
  vreg_ADD_to_real rd 2 1

private theorem extract_high64_to_bits_truncate_eq_ofInt_div (p : Int) :
    (Sail.BitVec.extractLsb (to_bits_truncate (l := 128) p) 127 64 : BitVec 64) =
      BitVec.ofInt 64 (p / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', to_bits_truncate,
        Sail.get_slice_int, Nat.shiftRight_eq_div_pow]
  omega

private theorem mulhs_eq_sail_mulh_value (v1 v2 : BitVec 64) :
    mulhs v1 v2 =
      mult_to_bits_half (l := LeanRV64D.Functions.xlen)
        Signedness.Signed Signedness.Signed v1 v2 VectorHalf.High := by
  unfold mulhs mult_to_bits_half LeanRV64D.Functions.xlen
  simp only
  change BitVec.ofInt 64 (v1.toInt * v2.toInt / 2^64) =
    BitVec.setWidth 64
      (Sail.BitVec.extractLsb
        (to_bits_truncate (l := 128) (v1.toInt * v2.toInt)) 127 64)
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

private theorem mulh_correction_eq_mulhs (x y : BitVec 64) :
    jolt_mulh_value x y = mulhs x y := by
  by_cases hx : x.toNat < 9223372036854775808
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [jolt_mulh_value, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      omega
    · rw [jolt_mulh_value, jolt_movsign_value_eq_zero_of_toNat_lt_half x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_toNat_lt_half x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_pos_neg_arith x.toNat y.toNat
  · by_cases hy : y.toNat < 9223372036854775808
    · rw [jolt_mulh_value, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_zero_of_toNat_lt_half y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_half_le x hx, toInt_of_toNat_lt_half y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_pos_arith x.toNat y.toNat
    · rw [jolt_mulh_value, jolt_movsign_value_eq_neg_one_of_half_le x hx,
          jolt_movsign_value_eq_neg_one_of_half_le y hy]
      unfold jolt_mulhu_value mulhs
      rw [toInt_of_half_le x hx, toInt_of_half_le y hy]
      apply BitVec.eq_of_toNat_eq
      simp
      exact mulh_corr_neg_neg_arith x.toNat y.toNat

theorem execute_MULH_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhs v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhOp, mulhs_eq_sail_mulh_value, bind_pure_comp]

theorem jolt_mulh_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (jsf : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulh rs2 rs1 rd).run js = .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhs v1 v2) := by
  unfold jolt_mulh vreg_movsign_from_real vreg_MUL_from_real_vs2
    vreg_MULHU_from_real vreg_ADD vreg_ADD_to_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    readVReg, writeVReg, get, modify, modifyGet, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet, EStateM.get, EStateM.modifyGet]
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  simp only [h1, h2]
  simp
  let out := jolt_mulhu_value v1 v2 + jolt_movsign_value v1 * v2 +
    jolt_movsign_value v2 * v1
  obtain ⟨sf, hw⟩ := wX_shape rd out js.sail
  rw [show wX_bits rd
        (jolt_mulhu_value v1 v2 + jolt_movsign_value v1 * v2 +
          jolt_movsign_value v2 * v1) js.sail = .ok () sf by
    simpa [out] using hw]
  simp only
  refine ⟨_, rfl, ?_⟩
  change sf = stateAfterWrite js.sail rd (mulhs v1 v2)
  rw [wX_bits_eq_stateAfterWrite rd out js.sail sf hw]
  change stateAfterWrite js.sail rd (jolt_mulh_value v1 v2) =
    stateAfterWrite js.sail rd (mulhs v1 v2)
  rw [mulh_correction_eq_mulhs]

theorem jolt_mulh_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulh rs2 rs1 rd).run js) =
    (execute_MUL rs2 rs1 rd mulhOp).run js.sail :=
  rtype_eq_sail_uniform
    (f := mulhs)
    (execute_MULH_factored rs2 rs1 rd)
    (jolt_mulh_concrete rs2 rs1 rd hrd js hwf)

end
