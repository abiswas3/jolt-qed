import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
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

/-- Compatibility alias for the Jolt-ISA `MULH` program interpreter. -/
def jolt_mulh (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult :=
  JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)

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

The named `js1` through `js7` states are lecture-note checkpoints.  Each one is
the state immediately after one instruction in `JoltISA.mulhProgram` retires:

* `js1`: `v0 = sign(rs1)`
* `js2`: `v1 = sign(rs2)`
* `js3`: `v0 = sign(rs1) * rs2`
* `js4`: `v1 = sign(rs2) * rs1`
* `js5`: `v2 = unsigned_high(rs1 * rs2)`
* `js6`: `v2 = unsigned_high(rs1 * rs2) + sign(rs1) * rs2`
* `js7`: `rd = v2 + sign(rs2) * rs1`

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
  let sx := jolt_movsign_value v1
  let sy := jolt_movsign_value v2
  let p0 := sx * v2
  let p1 := sy * v1
  let hi := jolt_mulhu_value v1 v2
  let out := jolt_mulh_value v1 v2

  -- After `VirtualMovsign v0, rs1`.
  let js1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then sx else js.vregs r }
  -- After `VirtualMovsign v1, rs2`.
  let js2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then sy else js1.vregs r }
  -- After `MUL v0, v0, rs2`.
  let js3 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then p0 else js2.vregs r }
  -- After `MUL v1, v1, rs1`.
  let js4 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then p1 else js3.vregs r }
  -- After `MULHU v2, rs1, rs2`.
  let js5 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then hi else js4.vregs r }
  -- After `ADD v2, v2, v0`.
  let js6 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (2 : JoltISA.VReg) then hi + p0 else js5.vregs r }
  -- The final architectural write goes through Sail's `wX_bits`, so we use the
  -- standard shape lemma to name the resulting Sail state `sf`.
  obtain ⟨sf, hw⟩ := wX_shape rd out js.sail
  -- After `ADD rd, v2, v1`.
  let js7 : SailJoltState := { sail := sf, vregs := js6.vregs }

  -- The intermediate Jolt states above never change `sail`, so architectural
  -- reads that succeeded initially still succeed from those states.
  have h1_js4 : rX_bits rs1 js4.sail = .ok v1 js4.sail := by
    simpa [js4, js3, js2, js1] using h1
  have h2_js2 : rX_bits rs2 js2.sail = .ok v2 js2.sail := by
    simpa [js2, js1] using h2
  have h2_js4 : rX_bits rs2 js4.sail = .ok v2 js4.sail := by
    simpa [js4, js3, js2, js1] using h2
  have hstep1 :
      JoltISA.execInstr (.Movsign (.vreg (0 : JoltISA.VReg)) (.xreg rs1)) js =
        .ok RETIRE_SUCCESS js1 := by
    simpa [js1, sx] using
      (JoltISA.execInstr_movsign_xreg_vreg_run (vd := (0 : JoltISA.VReg)) (rs := rs1) js v1 h1)
  have hstep2 :
      JoltISA.execInstr (.Movsign (.vreg (1 : JoltISA.VReg)) (.xreg rs2)) js1 =
        .ok RETIRE_SUCCESS js2 := by
    simpa [js2, sy] using
      (JoltISA.execInstr_movsign_xreg_vreg_run (vd := (1 : JoltISA.VReg)) (rs := rs2) js1 v2
        (by simpa [js1] using h2))
  have hstep3 :
      JoltISA.execInstr (.MUL (.vreg (0 : JoltISA.VReg)) (.vreg (0 : JoltISA.VReg)) (.xreg rs2)) js2 =
        .ok RETIRE_SUCCESS js3 := by
    simpa [js3, p0, sx, js2] using
      (JoltISA.execInstr_mul_vreg_xreg_vreg_run (vd := (0 : JoltISA.VReg)) (lhs := (0 : JoltISA.VReg))
        (rhs := rs2) js2 v2 h2_js2)
  have hstep4 :
      JoltISA.execInstr (.MUL (.vreg (1 : JoltISA.VReg)) (.vreg (1 : JoltISA.VReg)) (.xreg rs1)) js3 =
        .ok RETIRE_SUCCESS js4 := by
    simpa [js4, p1, sy, js3, js2, js1] using
      (JoltISA.execInstr_mul_vreg_xreg_vreg_run (vd := (1 : JoltISA.VReg)) (lhs := (1 : JoltISA.VReg))
        (rhs := rs1) js3 v1 (by simpa [js3, js2, js1] using h1))
  have hstep5 :
      JoltISA.execInstr (.MULHU (.vreg (2 : JoltISA.VReg)) (.xreg rs1) (.xreg rs2)) js4 =
        .ok RETIRE_SUCCESS js5 := by
    simpa [js5, hi] using
      (JoltISA.execInstr_mulhu_xreg_xreg_vreg_run (vd := (2 : JoltISA.VReg)) (lhs := rs1)
        (rhs := rs2) js4 v1 v2 h1_js4 h2_js4)
  have hstep6 :
      JoltISA.execInstr (.ADD (.vreg (2 : JoltISA.VReg)) (.vreg (2 : JoltISA.VReg)) (.vreg (0 : JoltISA.VReg))) js5 =
        .ok RETIRE_SUCCESS js6 := by
    simpa [js6, js5, js4, js3, js2, js1, hi, p0] using
      (JoltISA.execInstr_add_vreg_vreg_vreg_run (vd := (2 : JoltISA.VReg)) (lhs := (2 : JoltISA.VReg))
        (rhs := (0 : JoltISA.VReg)) js5)
  have hw_js6 : wX_bits rd (js6.vregs (2 : JoltISA.VReg) + js6.vregs (1 : JoltISA.VReg)) js6.sail =
      .ok () sf := by
    simpa [js6, js5, js4, js3, js2, js1, out, hi, p0, p1] using hw
  have hstep7 :
      JoltISA.execInstr (.ADD (.xreg rd) (.vreg (2 : JoltISA.VReg)) (.vreg (1 : JoltISA.VReg))) js6 =
        .ok RETIRE_SUCCESS js7 := by
    simpa [js7] using
      (JoltISA.execInstr_add_vreg_vreg_xreg_run (rd := rd) (lhs := (2 : JoltISA.VReg))
        (rhs := (1 : JoltISA.VReg)) js6 sf hw_js6)
  refine ⟨js7, ?_, ?_⟩
  · simp only [JoltISA.mulhProgram, JoltISA.execProgram_instr, EStateM.run,
      bind, EStateM.bind]
    rw [hstep1]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep2]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep3]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep4]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep5]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep6]
    simp only [RETIRE_SUCCESS, EStateM.bind]
    rw [hstep7]
    simp [JoltISA.execProgram, RETIRE_SUCCESS, pure, EStateM.pure, js7]
  -- The program has retired.  The last obligation is just to identify the Sail
  -- state produced by `wX_bits` with `stateAfterWrite` at the pure Jolt value.
  change sf = stateAfterWrite js.sail rd (jolt_mulh_value v1 v2)
  rw [wX_bits_eq_stateAfterWrite rd out js.sail sf hw]

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
  simpa [mulh_correction_eq_mulhs] using hsail

/-- Compatibility wrapper for older call sites that still refer to `jolt_mulh`
instead of the program-level `JoltISA.mulhProgram`. -/
theorem jolt_mulh_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (jsf : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulh rs2 rs1 rd).run js = .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = stateAfterWrite js.sail rd (mulhs v1 v2) := by
  simpa [jolt_mulh] using mulhProgram_concrete rs2 rs1 rd hrd js hwf

/-- Main program-level theorem: interpreting the Jolt ISA `MULH` expansion has
the same projected architectural result as Sail's `MULH` semantics. -/
theorem mulhProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.mulhProgram rs2 rs1 rd)).run js) =
    (execute_MUL rs2 rs1 rd mulhOp).run js.sail :=
  rtype_eq_sail_uniform
    (f := mulhs)
    (execute_MULH_factored rs2 rs1 rd)
    (mulhProgram_concrete rs2 rs1 rd hrd js hwf)

/-- Compatibility theorem for older names: `jolt_mulh` is just the program
interpreter for `JoltISA.mulhProgram`. -/
theorem jolt_mulh_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulh rs2 rs1 rd).run js) =
    (execute_MUL rs2 rs1 rd mulhOp).run js.sail := by
  simpa [jolt_mulh] using mulhProgram_eq_sail rs2 rs1 rd hrd js hwf

end
