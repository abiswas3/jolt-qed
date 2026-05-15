import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULH: Rust inline sequence = Sail MULH

This file is deliberately organized as a small proof-engineering template for
M-extension instructions that do not use advice.

The theorem we ultimately care about is program-level:

```
projectResult ((JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)).run js)
  =
(execute_MUL rs2 rs1 rd mulhOp).run js.sail
```

That statement is the right long-term shape because `JoltISA.mulhProgram` is
data.  Today it is handwritten, but later it should be the direct output of a
Rust-to-Lean extractor.  The proof should therefore explain why this program is
equivalent to Sail; it should not hide behind a second handwritten monadic
implementation.

The proof has three conceptual layers:

1. `JoltISA.mulhProgram` is the literal Rust inline sequence.
2. `mulhProgram_eval_jolt_value` executes that program and shows the
   value written to `rd` is `jolt_mulh_value`.
3. `mulh_correction_eq_mulhs` is the arithmetic lemma connecting that Jolt
   value to the Sail/RISC-V signed-high multiply value `mulhs`.

The Rust inline sequence, with the allocator choices fixed to virtual registers
`0`, `1`, and `2`, is:

```
VirtualMovsign v_sx, rs1
VirtualMovsign v_sy, rs2
MUL            v_sx, v_sx, rs2
MUL            v_sy, v_sy, rs1
MULHU          v_tmp, rs1, rs2
ADD            v_tmp, v_tmp, v_sx
ADD            rd,    v_tmp, v_sy
```
-/

def mulhOp : mul_op :=
  { result_part := VectorHalf.High
    signed_rs1 := Signedness.Signed
    signed_rs2 := Signedness.Signed }

/-- The pure value written by the Rust `MULH` inline sequence. -/
def jolt_mulh_value (x y : BitVec 64) : BitVec 64 :=
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
/-- The local `mulhs` value agrees with Sail's generic signed/signed high-half
multiply operator. -/
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
/-- The unsigned-high product plus the two sign corrections computed by Jolt is
exactly the signed-high product required by RV64 `MULH`. -/
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
/-- Factor Sail's generated `execute_MUL` body for `MULH` into the simple shape
used by the generic R-type equivalence bridge. -/
theorem execute_MULH_factored (rs2 rs1 rd : regidx) :
    execute_MUL rs2 rs1 rd mulhOp = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (mulhs v1 v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_MUL, mulhOp, mulhs_eq_sail_mulh_value, bind_pure_comp]

/-- Evaluate the Jolt `MULH` expansion to the pure value it writes.

This theorem is the monadic part of the proof.  It assumes the two architectural
register reads have already succeeded and then follows the `JoltISA.Program`
one instruction at a time.  The conclusion is intentionally phrased in terms of
`jolt_mulh_value`, not `mulhs`: this theorem knows about the Rust/Jolt
expansion, but it does not know the arithmetic fact that the expansion equals
the RISC-V signed-high multiply.

The named states are lecture-note checkpoints.  Each one is the state
immediately after one instruction in `JoltISA.mulhProgram` retires:

* `js_afterRs1SignMask`: `v0 = sign(rs1)`
* `js_afterRs2SignMask`: `v1 = sign(rs2)`
* `js_afterRs1CorrectionMul`: `v0 = sign(rs1) * rs2`
* `js_afterRs2CorrectionMul`: `v1 = sign(rs2) * rs1`
* `js_afterMulhu`: `v2 = unsigned_high(rs1 * rs2)`
* `js_afterAddRs1Correction`: `v2 = unsigned_high(rs1 * rs2) + sign(rs1) * rs2`
* `js_afterFinalAdd`: `rd = v2 + sign(rs2) * rs1`

Keeping these states explicit is verbose, but it makes the proof audit-friendly:
every virtual register write can be compared directly with the Rust sequence. -/
theorem mulhProgram_eval_jolt_value (rs2 rs1 rd : regidx)
    (js : SailJoltState) (v1 v2 : BitVec 64)
    (h1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (jolt_mulh_value v1 v2) := by
  -- Pure names for the values the Rust expansion computes.  These are not
  -- additional definitions in the trusted story; they are local proof names
  -- that keep later state updates readable.
  let rs1SignMask := jolt_movsign_value v1
  let rs2SignMask := jolt_movsign_value v2
  let rs1CorrectionProduct := rs1SignMask * v2
  let rs2CorrectionProduct := rs2SignMask * v1
  let unsignedHighProduct := jolt_mulhu_value v1 v2
  let mulhJoltResult := jolt_mulh_value v1 v2

  -- After `VirtualMovsign v0, rs1`.
  let js_afterRs1SignMask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then rs1SignMask else js.vregs r }
  -- After `VirtualMovsign v1, rs2`.
  let js_afterRs2SignMask : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (1 : JoltISA.VReg) then rs2SignMask else js_afterRs1SignMask.vregs r }
  -- After `MUL v0, v0, rs2`.
  let js_afterRs1CorrectionMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (0 : JoltISA.VReg) then rs1CorrectionProduct
        else js_afterRs2SignMask.vregs r }
  -- After `MUL v1, v1, rs1`.
  let js_afterRs2CorrectionMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (1 : JoltISA.VReg) then rs2CorrectionProduct
        else js_afterRs1CorrectionMul.vregs r }
  -- After `MULHU v2, rs1, rs2`.
  let js_afterMulhu : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (2 : JoltISA.VReg) then unsignedHighProduct
        else js_afterRs2CorrectionMul.vregs r }
  -- After `ADD v2, v2, v0`.
  let js_afterAddRs1Correction : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = (2 : JoltISA.VReg) then unsignedHighProduct + rs1CorrectionProduct
        else js_afterMulhu.vregs r }
  -- The final architectural write goes through Sail's `wX_bits`, so we use the
  -- standard shape lemma to name the resulting Sail state.
  obtain ⟨s_afterFinalAdd, h_final_add_write⟩ := wX_shape rd mulhJoltResult js.sail
  -- After `ADD rd, v2, v1`.
  let js_afterFinalAdd : SailJoltState :=
    { sail := s_afterFinalAdd, vregs := js_afterAddRs1Correction.vregs }

  -- The intermediate Jolt states above never change `sail`, so architectural
  -- reads that succeeded initially still succeed from those states.
  have h_rs1_reads_v1_after_rs2_correction_mul :
      rX_bits rs1 js_afterRs2CorrectionMul.sail =
        .ok v1 js_afterRs2CorrectionMul.sail := by
    simpa (config := { decide := true }) only [js_afterRs2CorrectionMul, js_afterRs1CorrectionMul, js_afterRs2SignMask,
      js_afterRs1SignMask] using h1
  have h_rs2_reads_v2_after_rs2_sign_mask :
      rX_bits rs2 js_afterRs2SignMask.sail = .ok v2 js_afterRs2SignMask.sail := by
    simpa (config := { decide := true }) only [js_afterRs2SignMask, js_afterRs1SignMask] using h2
  have h_rs2_reads_v2_after_rs2_correction_mul :
      rX_bits rs2 js_afterRs2CorrectionMul.sail =
        .ok v2 js_afterRs2CorrectionMul.sail := by
    simpa (config := { decide := true }) only [js_afterRs2CorrectionMul, js_afterRs1CorrectionMul, js_afterRs2SignMask,
      js_afterRs1SignMask] using h2
  have h_rs1_sign_mask_succeeds :
      JoltISA.execInstr (.VirtualMovsign (.vreg (0 : JoltISA.VReg)) (.xreg rs1)) js =
        .ok RETIRE_SUCCESS js_afterRs1SignMask := by
    simpa (config := { decide := true }) only [js_afterRs1SignMask, rs1SignMask] using
      (JoltISA.movsign_run_vreg_xreg (vd := (0 : JoltISA.VReg)) (rs := rs1) js v1 h1)
  have h_rs2_sign_mask_succeeds :
      JoltISA.execInstr (.VirtualMovsign (.vreg (1 : JoltISA.VReg)) (.xreg rs2))
        js_afterRs1SignMask =
        .ok RETIRE_SUCCESS js_afterRs2SignMask := by
    simpa (config := { decide := true }) only [js_afterRs2SignMask, rs2SignMask] using
      (JoltISA.movsign_run_vreg_xreg (vd := (1 : JoltISA.VReg)) (rs := rs2)
        js_afterRs1SignMask v2 (by simpa (config := { decide := true }) only [js_afterRs1SignMask] using h2))
  have h_rs1_correction_mul_succeeds :
      JoltISA.execInstr (.MUL (.vreg (0 : JoltISA.VReg)) (.vreg (0 : JoltISA.VReg))
        (.xreg rs2)) js_afterRs2SignMask =
        .ok RETIRE_SUCCESS js_afterRs1CorrectionMul := by
    simpa (config := { decide := true }) only [js_afterRs1CorrectionMul, rs1CorrectionProduct, rs1SignMask,
      js_afterRs2SignMask] using
      (JoltISA.mul_run_vreg_vreg_xreg (vd := (0 : JoltISA.VReg)) (lhs := (0 : JoltISA.VReg))
        (rhs := rs2) js_afterRs2SignMask v2 h_rs2_reads_v2_after_rs2_sign_mask)
  have h_rs2_correction_mul_succeeds :
      JoltISA.execInstr (.MUL (.vreg (1 : JoltISA.VReg)) (.vreg (1 : JoltISA.VReg))
        (.xreg rs1)) js_afterRs1CorrectionMul =
        .ok RETIRE_SUCCESS js_afterRs2CorrectionMul := by
    simpa (config := { decide := true }) only [js_afterRs2CorrectionMul, rs2CorrectionProduct, rs2SignMask,
      js_afterRs1CorrectionMul, js_afterRs2SignMask, js_afterRs1SignMask] using
      (JoltISA.mul_run_vreg_vreg_xreg (vd := (1 : JoltISA.VReg)) (lhs := (1 : JoltISA.VReg))
        (rhs := rs1) js_afterRs1CorrectionMul v1
        (by simpa (config := { decide := true }) only [js_afterRs1CorrectionMul, js_afterRs2SignMask, js_afterRs1SignMask] using h1))
  have h_mulhu_succeeds :
      JoltISA.execInstr (.MULHU (.vreg (2 : JoltISA.VReg)) (.xreg rs1) (.xreg rs2))
        js_afterRs2CorrectionMul =
        .ok RETIRE_SUCCESS js_afterMulhu := by
    simpa (config := { decide := true }) only [js_afterMulhu, unsignedHighProduct] using
      (JoltISA.mulhu_run_vreg_xreg_xreg (vd := (2 : JoltISA.VReg)) (lhs := rs1)
        (rhs := rs2) js_afterRs2CorrectionMul v1 v2
        h_rs1_reads_v1_after_rs2_correction_mul h_rs2_reads_v2_after_rs2_correction_mul)
  have h_add_rs1_correction_succeeds :
      JoltISA.execInstr (.ADD (.vreg (2 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg))
        (.vreg (0 : JoltISA.VReg))) js_afterMulhu =
        .ok RETIRE_SUCCESS js_afterAddRs1Correction := by
    simpa (config := { decide := true }) only [js_afterAddRs1Correction, js_afterMulhu, js_afterRs2CorrectionMul,
      js_afterRs1CorrectionMul, js_afterRs2SignMask, js_afterRs1SignMask,
      unsignedHighProduct, rs1CorrectionProduct] using
      (JoltISA.add_run_vreg_vreg_vreg (vd := (2 : JoltISA.VReg)) (lhs := (2 : JoltISA.VReg))
        (rhs := (0 : JoltISA.VReg)) js_afterMulhu)
  have h_final_add_write_input :
      wX_bits rd
        (js_afterAddRs1Correction.vregs (2 : JoltISA.VReg) +
          js_afterAddRs1Correction.vregs (1 : JoltISA.VReg))
        js_afterAddRs1Correction.sail = .ok () s_afterFinalAdd := by
    simpa (config := { decide := true }) only [js_afterAddRs1Correction, js_afterMulhu, js_afterRs2CorrectionMul,
      js_afterRs1CorrectionMul, js_afterRs2SignMask, js_afterRs1SignMask,
      mulhJoltResult, unsignedHighProduct, rs1CorrectionProduct, rs2CorrectionProduct] using
      h_final_add_write
  have h_final_add_succeeds :
      JoltISA.execInstr (.ADD (.xreg rd) (.vreg (2 : JoltISA.VReg)) (.vreg (1 : JoltISA.VReg)))
        js_afterAddRs1Correction =
        .ok RETIRE_SUCCESS js_afterFinalAdd := by
    simpa (config := { decide := true }) only [js_afterFinalAdd] using
      (JoltISA.add_run_xreg_vreg_vreg (rd := rd) (lhs := (2 : JoltISA.VReg))
        (rhs := (1 : JoltISA.VReg)) js_afterAddRs1Correction s_afterFinalAdd
        h_final_add_write_input)
  refine ⟨js_afterFinalAdd, ?_, ?_⟩
  · simp only [JoltISA.mulhProgram, JoltISA.execProgram_instr, EStateM.run,
      bind, EStateM.bind]
    rw [h_rs1_sign_mask_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_rs2_sign_mask_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_rs1_correction_mul_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_rs2_correction_mul_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_mulhu_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_add_rs1_correction_succeeds]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [h_final_add_succeeds]
    simp [JoltISA.execProgram, RETIRE_SUCCESS, pure, EStateM.pure, js_afterFinalAdd]
  -- The program has retired.  The last obligation is just to identify the Sail
  -- state produced by `wX_bits` with `stateAfterWrite` at the pure Jolt value.
  change s_afterFinalAdd = stateAfterWrite js.sail rd (jolt_mulh_value v1 v2)
  rw [wX_bits_eq_stateAfterWrite rd mulhJoltResult js.sail s_afterFinalAdd h_final_add_write]

/-- Combine the Jolt-value evaluation theorem with the arithmetic correction
lemma.  This is the theorem shape expected by the generic R-type equivalence
bridge: it packages successful source reads, successful Jolt execution, and the
final architectural state written with the Sail value `mulhs`. -/
theorem mulhProgram_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (jsf : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhs v1 v2) := by
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  obtain ⟨jsf, hrun, hsail⟩ := mulhProgram_eval_jolt_value rs2 rs1 rd js v1 v2 h1 h2
  refine ⟨jsf, v1, v2, h1, h2, hrun, ?_⟩

  -- The execution theorem leaves `rd` containing the literal Jolt MULH value.
  have h_final_jolt_value :
      jsf.sail = stateAfterWrite js.sail rd (jolt_mulh_value v1 v2) :=
    hsail

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's correction sequence is Sail's MULH value.
  have h_mulh_value :
      jolt_mulh_value v1 v2 = mulhs v1 v2 := by
    -- NOTE: The core math theorem.
    exact mulh_correction_eq_mulhs v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_mulh_value]
  exact h_final_jolt_value

/-- Main program-level theorem: interpreting the Jolt ISA `MULH` expansion has
the same projected architectural result as Sail's `MULH` semantics. -/
theorem mulhProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)).run js) =
    (execute_MUL rs2 rs1 rd mulhOp).run js.sail := by
  obtain ⟨js_afterFinalAdd, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    mulhProgram_concrete rs2 rs1 rd hrd js hwf

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_MULH_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (mulhs v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (mulhs v1 v2) js.sail s' h_write).symm

end
