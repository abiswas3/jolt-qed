import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.JoltISA.Semantics.InstructionRunHelpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `divwProgram`

The 21 steps of `divwProgram` split into **six** phases (one more than
DIV's five). The extra phase is `phase_rem_nonneg` — DIVW supplies a
32-bit `|remainder|` advice inside a 64-bit BitVec, so it must verify
the upper 33 bits are zero (`SRAI v1 31 = 0`). DIV doesn't need this
because its `|rem|` is naturally 64-bit unsigned.

This file mirrors `Div_phase_helpers.lean` in structure and reuses the
generic `_run`/`_run_ex` helpers from there (`vreg_advice_run_ex`,
`vreg_MUL_run_ex`, `vreg_SRAI_run_ex`, etc.). New helpers are added for
the DIVW-specific primitives (`vreg_sign_extend_word*`,
`vreg_change_divisor_w`, `vreg_assert_valid_div0_v`).

Phase definitions and phase-run lemmas live in the `Divw` namespace
to avoid clashing with DIV's flat-namespaced `phase_*` and
`phase_*_run`. Per-instruction `_run`/`_run_ex` helpers are not
namespaced — they're additive to the existing pool from
`Div_phase_helpers`.

The phase-run lemmas prove each fragment by reducing the local
`JoltISA.Program` to its instruction runs.
-/

-- ============================================================================
-- New per-instruction `_run` lemmas (DIVW primitives)
-- ============================================================================
-- The generic ones (`vreg_advice_run`, `vreg_MUL_run`, `vreg_SRAI_run`,
-- `vreg_assert_eq_run_*`, `vreg_assert_valid_unsigned_remainder_run_*`,
-- and their `_ex` variants) come for free via the import of
-- `Div_phase_helpers`. The lemmas below characterise the new
-- DIVW-specific primitives introduced in `Primitives.lean`.

/-- `vreg_sign_extend_word vd vs1`: writes
`sign_extend (extractLsb (vs1) 31 0)` to `vd`. Pure. -/
theorem vreg_sign_extend_word_run (vd vs1 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.VirtualSignExtendWord (.vreg vd) (.vreg vs1))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0)
          else js.vregs r } :=
  JoltISA.virtual_sign_extend_word_run_vreg_vreg vd vs1 js

/-- Existential variant of `vreg_sign_extend_word_run`. -/
theorem vreg_sign_extend_word_run_ex (vd vs1 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg vd) (.vreg vs1))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd
        then sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_sign_extend_word_run vd vs1 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- `vreg_sign_extend_word_from_real vd rs1`: reads real `rs1`,
sign-extends low 32 bits to 64, writes virtual `vd`. -/
theorem vreg_sign_extend_word_from_real_run
    (vd : BitVec 7) (rs1 : regidx) (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    (JoltISA.execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs1))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)
          else js.vregs r } :=
  JoltISA.virtual_sign_extend_word_run_vreg_xreg vd rs1 js rs1_val hrs1

/-- Existential variant of `vreg_sign_extend_word_from_real_run`. -/
theorem vreg_sign_extend_word_from_real_run_ex
    (vd : BitVec 7) (rs1 : regidx) (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd
        then sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_sign_extend_word_from_real_run vd rs1 js rs1_val hrs1
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- `vreg_sign_extend_word_to_real rd vs1`: reads virtual `vs1`,
sign-extends low 32 bits, writes real `rd`. -/
theorem vreg_sign_extend_word_to_real_run
    (rd : regidx) (vs1 : BitVec 7)
    (js : SailJoltState) (s' : SailState)
    (hwrite :
      wX_bits rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0))
        js.sail
        = .ok () s') :
    (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg vs1))).run js =
      .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
  JoltISA.virtual_sign_extend_word_run_xreg_vreg rd vs1 js s' hwrite

/-- `vreg_change_divisor_w vd vs1 vs2`: 32-bit version of
`vreg_change_divisor`, reading from virtual sign-extended copies.
Pure. -/
theorem vreg_change_divisor_w_run
    (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    (JoltISA.execInstr (.VirtualChangeDivisorW vd vs1 vs2)).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then change_divisor_w_value (js.vregs vs1) (js.vregs vs2)
          else js.vregs r } :=
  JoltISA.virtual_change_divisor_w_run vd vs1 vs2 js

/-- Existential variant of `vreg_change_divisor_w_run`. -/
theorem vreg_change_divisor_w_run_ex
    (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execInstr (.VirtualChangeDivisorW vd vs1 vs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = change_divisor_w_value (js.vregs vs1) (js.vregs vs2) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd
        then change_divisor_w_value (js.vregs vs1) (js.vregs vs2)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_change_divisor_w_run vd vs1 vs2 js
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- `vreg_assert_valid_div0_v vd vq` — success branch. Virtual-divisor
variant: when the guard `¬ (s.vregs vd = 0 ∧ s.vregs vq ≠ -1)` holds,
the assert passes through with no state change. -/
theorem vreg_assert_valid_div0_v_run_ok
    (vd vq : BitVec 7) (js : SailJoltState)
    (hguard : ¬ (js.vregs vd = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64))) :
    (JoltISA.execInstr (.VirtualAssertValidDiv0V vd vq)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_valid_div0_v_run_ok vd vq js hguard

/-- `vreg_assert_valid_div0_v vd vq` — failure branch. -/
theorem vreg_assert_valid_div0_v_run_err
    (vd vq : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs vd = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64)) :
    (JoltISA.execInstr (.VirtualAssertValidDiv0V vd vq)).run js =
      .error
        (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
        js :=
  JoltISA.virtual_assert_valid_div0_v_run_err vd vq js hguard

-- ============================================================================
-- Phase definitions and phase-run lemmas
-- ============================================================================
-- Wrapped in `namespace Divw` to avoid clashing with the flat-namespaced
-- DIV phase definitions imported via `Div_phase_helpers`.

namespace Divw

/-- Phase 1 — advice loads + sign-extension prologue + div0 check.

Loads the oracle's `quotient` and `|remainder|` into `v0` and `v1`,
sign-extends `rs1` into `v6` and `rs2` into `v5` (so that the rest of
the program can run on virtual sign-extended copies), and asserts the
div-by-zero constraint on the *sign-extended* divisor `v5`. -/
def phase_setup (rs1 rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltISA.Program :=
  .instr (.VirtualAdvice 0 quotient) <|
  .instr (.VirtualAdvice 1 rem_abs) <|
  .instr (.VirtualSignExtendWord (.vreg 6) (.xreg rs1)) <|
  .instr (.VirtualSignExtendWord (.vreg 5) (.xreg rs2)) <|
  .instr (.VirtualAssertValidDiv0V 5 0) <|
  .done RETIRE_SUCCESS

/-- Phase 2 — adjusted divisor + quotient-fits-in-32-bits check.

Computes `v2 = change_divisor_w(v6, v5)` (the `(i32::MIN, -1)` overflow
fixup at 32-bit width), then asserts that the quotient advice itself
fits in 32 bits via the round-trip `v3 = sext(v0); v3 = v0`. -/
def phase_overflow_check : JoltISA.Program :=
  .instr (.VirtualChangeDivisorW 2 6 5) <|
  .instr (.VirtualSignExtendWord (.vreg 3) (.vreg 0)) <|
  .instr (.VirtualAssertEQ 3 0) <|
  .done RETIRE_SUCCESS

/-- Phase 3 — remainder-non-negative check (DIVW-only, no DIV analogue).

-- WARNING: MISALIGNED — the Rust inline sequence uses `SRAI rem 31` but this
-- should be `SRAI rem 32` to correctly check `rem < 2^32` (fits in u32).
-- With shift 31, the case rs1_low = i32::MIN, rs2_low = 0 gives rem = 2^31
-- which fails the check, yet is the unique valid advice for that input.
-- See bug_reports/divw.md. The Rust fix is to change the shift from 31 to 32.

Asserts `SRAI v1 32 = x0`, which holds iff the upper 32 bits of the
`|remainder|` advice are zero — i.e. `rem_abs.toNat < 2^32` (fits in u32).
The DIV sequence doesn't need this because its `|rem|` is a full 64-bit value.
For DIVW the `|rem|` lives inside a 64-bit BitVec but represents a u32,
so the high half must be checked explicitly. -/
def phase_rem_nonneg : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg 4) (.vreg 1) (32 : BitVec 6) <|
  .instr (.VirtualAssertEQReal 4 (regidx.Regidx 0)) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — reconstruct signed remainder, sum, assert equals
sign-extended dividend `v6`.

`signed_rem` is `(rem XOR sign(dividend)) - sign(dividend)` at 32-bit
width (`shamt = 31`), reading the dividend from the sign-extended
virtual copy `v6` rather than the real `rs1`. The guard then checks
`q*adj + signed_rem = sext(rs1)`. -/
def phase_quotient_product : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg 4) (.vreg 6) (31 : BitVec 6) <|
  .instr (.XOR (.vreg 5) (.vreg 1) (.vreg 4)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 4)) <|
  .instr (.MUL (.vreg 3) (.vreg 0) (.vreg 2)) <|
  .instr (.ADD (.vreg 3) (.vreg 3) (.vreg 5)) <|
  .instr (.VirtualAssertEQ 3 6) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — compute `|adj_div|` (32-bit shamt) + `|rem| < |adj_div|` check.

Same shape as DIV's phase 4 but with `shamt = 31` instead of `63`,
operating on the virtual sign-extended adjusted divisor in `v2`. -/
def phase_remainder_bound : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg 4) (.vreg 2) (31 : BitVec 6) <|
  .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 4)) <|
  .instr (.SUB (.vreg 3) (.vreg 3) (.vreg 4)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 1 3) <|
  .done RETIRE_SUCCESS

/-- Phase 6 — sign-extend writeback `rd := SignExtendWord(v0)`.

Writes the validated quotient into the real destination register,
sign-extending its low 32 bits. Replaces DIV's plain `ADDI rd, v0, 0`
move because the 32-bit quotient must be sign-extended to 64 bits per
the RV64M `DIVW` spec. -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg 0)) <|
  .done RETIRE_SUCCESS

-- ----------------------------------------------------------------------------
-- Phase-run lemmas (completeness side)
-- ----------------------------------------------------------------------------

/-- Phase 1 — advice loads + sign-extension prologue + div0 check. -/
theorem phase_setup_run
    (rs1 rs2 : regidx) (q rem : BitVec 64) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 :
      ¬ (sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64 ∧
         q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs1 rs2 q rem)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 5 = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨s1, h1, hs1_v0, hs1_pres, hs1_sail⟩ := vreg_advice_run_ex 0 q js
  obtain ⟨s2, h2, hs2_v1, hs2_pres, hs2_sail⟩ := vreg_advice_run_ex 1 rem s1
  obtain ⟨s3, h3, hs3_v6, hs3_pres, hs3_sail⟩ :=
    vreg_sign_extend_word_from_real_run_ex 6 rs1 s2 dividend
      ((hs2_sail.trans hs1_sail).symm ▸ hrs1)
  obtain ⟨s4, h4, hs4_v5, hs4_pres, hs4_sail⟩ :=
    vreg_sign_extend_word_from_real_run_ex 5 rs2 s3 divisor
      ((hs3_sail.trans (hs2_sail.trans hs1_sail)).symm ▸ hrs2)
  have hs4_v0 : s4.vregs 0 = q :=
    (hs4_pres 0 (by decide)).trans ((hs3_pres 0 (by decide)).trans
      ((hs2_pres 0 (by decide)).trans hs1_v0))
  have hs4_v1 : s4.vregs 1 = rem :=
    (hs4_pres 1 (by decide)).trans ((hs3_pres 1 (by decide)).trans hs2_v1)
  have hs4_v6 : s4.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs4_pres 6 (by decide)).trans hs3_v6
  have hguard : ¬ (s4.vregs 5 = 0#64 ∧ s4.vregs 0 ≠ (-1 : BitVec 64)) := by
    rw [hs4_v5, hs4_v0]; exact hguard_div0
  have h5 := vreg_assert_valid_div0_v_run_ok 5 0 s4 hguard
  have hs4_sail_orig : s4.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v5, hs4_v6, hs4_sail_orig⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s4 h5]
  rfl

/-- Phase 2 — adjusted divisor + 32-bit quotient-fits check. -/
theorem phase_overflow_check_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hadj : adj = change_divisor_w_value sext_dividend sext_divisor)
    (hguard_q_fits :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q) :
    ∃ js',
      (JoltISA.execProgram phase_overflow_check).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 = sext_divisor ∧
      js'.vregs 6 = sext_dividend ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  obtain ⟨s1, h1, hs1_v2, hs1_pres, hs1_sail⟩ := vreg_change_divisor_w_run_ex 2 6 5 js
  obtain ⟨s2, h2, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_sign_extend_word_run_ex 3 0 s1
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v5 : s1.vregs 5 = sext_divisor := (hs1_pres 5 (by decide)).trans h_v5
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v2_eq : s1.vregs 2 = adj := by rw [hs1_v2, h_v6, h_v5]; exact hadj.symm
  have hs2_v0 : s2.vregs 0 = q := (hs2_pres 0 (by decide)).trans hs1_v0
  have hs2_v1 : s2.vregs 1 = rem := (hs2_pres 1 (by decide)).trans hs1_v1
  have hs2_v2 : s2.vregs 2 = adj := (hs2_pres 2 (by decide)).trans hs1_v2_eq
  have hs2_v5 : s2.vregs 5 = sext_divisor := (hs2_pres 5 (by decide)).trans hs1_v5
  have hs2_v6 : s2.vregs 6 = sext_dividend := (hs2_pres 6 (by decide)).trans hs1_v6
  have hs2_v3_eq : s2.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) := by
    rw [hs2_v3, hs1_v0]
  have hguard : s2.vregs 3 = s2.vregs 0 := by rw [hs2_v3_eq, hs2_v0]; exact hguard_q_fits
  have h3 := vreg_assert_eq_run_ok 3 0 s2 hguard
  have hs2_sail_orig : s2.sail = js.sail := hs2_sail.trans hs1_sail
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v5, hs2_v6, hs2_sail_orig⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s2 h3]
  rfl

-- WARNING: MISALIGNED — shift changed from 31 to 32 to match the required Rust fix.
-- See bug_reports/divw.md for full analysis.
/-- Phase 3 — DIVW-only `|rem|` ≥ 0 (as u32) check. -/
theorem phase_rem_nonneg_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail)
    (hguard_rem_nonneg : shift_bits_right_arith rem (32 : BitVec 6) = 0#64) :
    ∃ js',
      (JoltISA.execProgram phase_rem_nonneg).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 = sext_divisor ∧
      js'.vregs 6 = sext_dividend ∧
      js'.sail = js.sail := by
  unfold phase_rem_nonneg
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 1 32 js
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v5 : s1.vregs 5 = sext_divisor := (hs1_pres 5 (by decide)).trans h_v5
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs 4 = shift_bits_right_arith rem (32 : BitVec 6) := by rw [hs1_v4, h_v1]
  have hx0_s1 : rX_bits (regidx.Regidx 0) s1.sail = .ok 0#64 s1.sail := hs1_sail.symm ▸ hx0
  have hguard : s1.vregs 4 = 0#64 := by rw [hs1_v4_eq]; exact hguard_rem_nonneg
  have h2 := vreg_assert_eq_real_run_ok 4 (regidx.Regidx 0) s1 0#64 hx0_s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_v1, hs1_v2, hs1_v5, hs1_v6, hs1_sail⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

/-- Phase 4 — signed-remainder reconstruction + `q*adj + signed_rem = sext(rs1)`. -/
theorem phase_quotient_product_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hguard_quotient_product :
        q * adj +
          ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31)
        = sext_dividend) :
    ∃ js',
      (JoltISA.execProgram phase_quotient_product).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 6 31 js
  obtain ⟨s2, h2, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 4 s1
  obtain ⟨s3, h3, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 4 s2
  obtain ⟨s4, h4, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex 3 0 2 s3
  obtain ⟨s5, h5, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex 3 3 5 s4
  have hs5_sail_orig : s5.sail = js.sail :=
    hs5_sail.trans (hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail)))
  -- Lookups on s1
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs 4 = sext_dividend.sshiftRight 31 := by rw [hs1_v4, h_v6]; rfl
  -- Lookups on s2
  have hs2_v4 : s2.vregs 4 = sext_dividend.sshiftRight 31 :=
    (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v5_eq : s2.vregs 5 = rem ^^^ sext_dividend.sshiftRight 31 := by
    rw [hs2_v5, hs1_v1, hs1_v4_eq]
  -- Lookups on s3
  have hs3_v4 : s3.vregs 4 = sext_dividend.sshiftRight 31 :=
    (hs3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5_eq : s3.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 := by
    rw [hs3_v5, hs2_v5_eq, hs2_v4]
  have hs3_v0 : s3.vregs 0 = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)).trans h_v0
  have hs3_v2 : s3.vregs 2 = adj :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)).trans h_v2
  -- Lookups on s4
  have hs4_v5 : s4.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs4_pres 5 (by decide)).trans hs3_v5_eq
  have hs4_v3_eq : s4.vregs 3 = q * adj := by rw [hs4_v3, hs3_v0, hs3_v2]
  -- Lookups on s5
  have hs5_v6 : s5.vregs 6 = sext_dividend :=
    ((hs5_pres 6 (by decide)).trans ((hs4_pres 6 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 6 (by decide)))).trans h_v6
  have hs5_v3_eq : s5.vregs 3 = q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) := by
    rw [hs5_v3, hs4_v3_eq, hs4_v5]
  -- Assert
  have hguard : s5.vregs 3 = s5.vregs 6 := by rw [hs5_v3_eq, hs5_v6]; exact hguard_quotient_product
  have h6 := vreg_assert_eq_run_ok 3 6 s5 hguard
  -- Post-condition
  have hs5_v0 : s5.vregs 0 = q :=
    ((hs5_pres 0 (by decide)).trans ((hs4_pres 0 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs 1 = rem :=
    ((hs5_pres 1 (by decide)).trans ((hs4_pres 1 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs 2 = adj :=
    ((hs5_pres 2 (by decide)).trans ((hs4_pres 2 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)))).trans h_v2
  refine ⟨s5, ?_, hs5_v0, hs5_v1, hs5_v2, hs5_sail_orig⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s5 h5]
  rw [JoltISA.execProgram_instr_run_retire _ _ s5 s5 h6]
  rfl

/-- Phase 5 — compute `|adj|` (32-bit shamt) + `|rem| < |adj|` check. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 2 31 js
  obtain ⟨s2, h2, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 3 2 4 s1
  obtain ⟨s3, h3, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 3 3 4 s2
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  -- Lookups on s1
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs 4 = adj.sshiftRight 31 := by rw [hs1_v4, h_v2]; rfl
  -- Lookups on s2
  have hs2_v4 : s2.vregs 4 = adj.sshiftRight 31 := (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs 3 = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  -- Lookups on s3
  have hs3_v3_eq : s3.vregs 3 = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  -- Assert
  have hguard : s3.vregs 3 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 3).toNat := by
    rw [hs3_v3_eq, hs3_v1]; exact hguard_rem_bound
  have h4 := vreg_assert_valid_unsigned_remainder_run_ok 1 3 s3 hguard
  -- Post-condition
  have hs3_v0 : s3.vregs 0 = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)).trans h_v0
  refine ⟨s3, ?_, hs3_v0, hs3_sail_orig⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

/-- Phase 6 — sign-extend writeback `rd := SignExtendWord(v0)`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
                   (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := vreg_sign_extend_word_to_real_run rd 0 js s' (by
      rw [h_v0]
      exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction; for `divwProgram_sound`)
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness — extract the div0 guard and post-state invariants
from a successful `phase_setup` run. -/
theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (JoltISA.execProgram (phase_setup rs1 rs2 q rem)).run js =
      .ok RETIRE_SUCCESS js₁) :
    ¬ (sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64 ∧
       q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 5 = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.sail = js.sail := by
  unfold phase_setup at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s1', hrun1_ex, hs1_v0, hs1_pres, hs1_sail⟩ := vreg_advice_run_ex 0 q js
  rw [hrun1_ex] at hrun1; cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2', hrun2_ex, hs2_v1, hs2_pres, hs2_sail⟩ := vreg_advice_run_ex 1 rem s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3', hrun3_ex, hs3_v6, hs3_pres, hs3_sail⟩ :=
    vreg_sign_extend_word_from_real_run_ex 6 rs1 s2 dividend
      ((hs2_sail.trans hs1_sail).symm ▸ hrs1)
  rw [hrun3_ex] at hrun3; cases hrun3
  obtain ⟨s4, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s4', hrun4_ex, hs4_v5, hs4_pres, hs4_sail⟩ :=
    vreg_sign_extend_word_from_real_run_ex 5 rs2 s3 divisor
      ((hs3_sail.trans (hs2_sail.trans hs1_sail)).symm ▸ hrs2)
  rw [hrun4_ex] at hrun4; cases hrun4
  obtain ⟨js_afterAssert, hrun5, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs4_v0 : s4.vregs 0 = q :=
    (hs4_pres 0 (by decide)).trans ((hs3_pres 0 (by decide)).trans
      ((hs2_pres 0 (by decide)).trans hs1_v0))
  have hs4_v1 : s4.vregs 1 = rem :=
    (hs4_pres 1 (by decide)).trans ((hs3_pres 1 (by decide)).trans hs2_v1)
  have hs4_v6 : s4.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs4_pres 6 (by decide)).trans hs3_v6
  have hs4_sail_orig : s4.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  by_cases hguard : s4.vregs 5 = 0#64 ∧ s4.vregs 0 ≠ (-1 : BitVec 64)
  · exfalso
    have herr := vreg_assert_valid_div0_v_run_err 5 0 s4 hguard
    rw [herr] at hrun5; cases hrun5
  · have hok := vreg_assert_valid_div0_v_run_ok 5 0 s4 hguard
    rw [hok] at hrun5; cases hrun5
    refine ⟨?_, hs4_v0, hs4_v1, hs4_v5, hs4_v6, hs4_sail_orig⟩
    rw [hs4_v5, hs4_v0] at hguard; exact hguard

/-- Phase 2 soundness — extract the quotient-fits-in-32 guard. -/
theorem phase_overflow_check_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hadj : adj = change_divisor_w_value sext_dividend sext_divisor)
    (hp : (JoltISA.execProgram phase_overflow_check).run js =
      .ok RETIRE_SUCCESS js₁) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 = sext_divisor ∧
    js₁.vregs 6 = sext_dividend ∧
    js₁.sail = js.sail := by
  unfold phase_overflow_check at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s1', hrun1_ex, hs1_v2, hs1_pres, hs1_sail⟩ := vreg_change_divisor_w_run_ex 2 6 5 js
  rw [hrun1_ex] at hrun1; cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2', hrun2_ex, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_sign_extend_word_run_ex 3 0 s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨js_afterAssert, hrun3, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v5 : s1.vregs 5 = sext_divisor := (hs1_pres 5 (by decide)).trans h_v5
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v2_eq : s1.vregs 2 = adj := by rw [hs1_v2, h_v6, h_v5]; exact hadj.symm
  have hs2_v0 : s2.vregs 0 = q := (hs2_pres 0 (by decide)).trans hs1_v0
  have hs2_v1 : s2.vregs 1 = rem :=
    (hs2_pres 1 (by decide)).trans ((hs1_pres 1 (by decide)).trans h_v1)
  have hs2_v2 : s2.vregs 2 = adj := (hs2_pres 2 (by decide)).trans hs1_v2_eq
  have hs2_v5 : s2.vregs 5 = sext_divisor := (hs2_pres 5 (by decide)).trans hs1_v5
  have hs2_v6 : s2.vregs 6 = sext_dividend := (hs2_pres 6 (by decide)).trans hs1_v6
  have hs2_v3_eq : s2.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) := by
    rw [hs2_v3, hs1_v0]
  have hs2_sail_orig : s2.sail = js.sail := hs2_sail.trans hs1_sail
  by_cases hguard : s2.vregs 3 = s2.vregs 0
  · have hok := vreg_assert_eq_run_ok 3 0 s2 hguard
    rw [hok] at hrun3; cases hrun3
    refine ⟨?_, hs2_v0, hs2_v1, hs2_v2, hs2_v5, hs2_v6, hs2_sail_orig⟩
    rw [hs2_v3_eq, hs2_v0] at hguard; exact hguard
  · exfalso
    have herr := vreg_assert_eq_run_err 3 0 s2 hguard
    rw [herr] at hrun3; cases hrun3

/-- Phase 3 soundness — extract the `|rem| ≥ 0` (as i32) guard. -/
theorem phase_rem_nonneg_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail)
    (hp : (JoltISA.execProgram phase_rem_nonneg).run js =
      .ok RETIRE_SUCCESS js₁) :
    shift_bits_right_arith rem (32 : BitVec 6) = 0#64 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 = sext_divisor ∧
    js₁.vregs 6 = sext_dividend ∧
  js₁.sail = js.sail := by
  unfold phase_rem_nonneg at hp
  obtain ⟨s1, hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 1 32 js
  rw [hrun1_ex _] at hp
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v5 : s1.vregs 5 = sext_divisor := (hs1_pres 5 (by decide)).trans h_v5
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs 4 = shift_bits_right_arith rem (32 : BitVec 6) := by rw [hs1_v4, h_v1]
  have hx0_s1 : rX_bits (regidx.Regidx 0) s1.sail = .ok 0#64 s1.sail := hs1_sail.symm ▸ hx0
  by_cases hguard : s1.vregs 4 = 0#64
  · have hok := vreg_assert_eq_real_run_ok 4 (regidx.Regidx 0) s1 0#64 hx0_s1 hguard
    rw [hok] at hrun2; cases hrun2
    refine ⟨?_, hs1_v0, hs1_v1, hs1_v2, hs1_v5, hs1_v6, hs1_sail⟩
    rw [← hs1_v4_eq]; exact hguard
  · exfalso
    have herr := vreg_assert_eq_real_run_err 4 (regidx.Regidx 0) s1 0#64 hx0_s1 hguard
    rw [herr] at hrun2; cases hrun2

/-- Phase 4 soundness — extract the division-equation guard. -/
theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hp : (JoltISA.execProgram phase_quotient_product).run js =
      .ok RETIRE_SUCCESS js₁) :
    q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31)
      = sext_dividend ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
  js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨s1, hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 6 31 js
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2', hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 4 s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3', hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 4 s2
  rw [hrun3_ex] at hrun3; cases hrun3
  obtain ⟨s4, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s4', hrun4_ex, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex 3 0 2 s3
  rw [hrun4_ex] at hrun4; cases hrun4
  obtain ⟨s5, hrun5, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s5', hrun5_ex, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex 3 3 5 s4
  rw [hrun5_ex] at hrun5; cases hrun5
  obtain ⟨js_afterAssert, hrun6, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  -- Lookups
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v6 : s1.vregs 6 = sext_dividend := (hs1_pres 6 (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs 4 = sext_dividend.sshiftRight 31 := by rw [hs1_v4, h_v6]; rfl
  have hs2_v4 : s2.vregs 4 = sext_dividend.sshiftRight 31 :=
    (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v5_eq : s2.vregs 5 = rem ^^^ sext_dividend.sshiftRight 31 := by
    rw [hs2_v5, hs1_v1, hs1_v4_eq]
  have hs3_v4 : s3.vregs 4 = sext_dividend.sshiftRight 31 :=
    (hs3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5_eq : s3.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 := by
    rw [hs3_v5, hs2_v5_eq, hs2_v4]
  have hs3_v0 : s3.vregs 0 = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)).trans h_v0
  have hs3_v2 : s3.vregs 2 = adj :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)).trans h_v2
  have hs4_v5 : s4.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs4_pres 5 (by decide)).trans hs3_v5_eq
  have hs4_v3_eq : s4.vregs 3 = q * adj := by rw [hs4_v3, hs3_v0, hs3_v2]
  have hs5_v3_eq : s5.vregs 3 = q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) := by
    rw [hs5_v3, hs4_v3_eq, hs4_v5]
  have hs5_v6 : s5.vregs 6 = sext_dividend :=
    ((hs5_pres 6 (by decide)).trans ((hs4_pres 6 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 6 (by decide)))).trans h_v6
  have hs5_sail_orig : s5.sail = js.sail :=
    hs5_sail.trans (hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail)))
  -- Derive post-state facts BEFORE cases hp (cases hp substitutes s5 → js₁).
  have hs5_v0 : s5.vregs 0 = q :=
    ((hs5_pres 0 (by decide)).trans ((hs4_pres 0 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs 1 = rem :=
    ((hs5_pres 1 (by decide)).trans ((hs4_pres 1 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs 2 = adj :=
    ((hs5_pres 2 (by decide)).trans ((hs4_pres 2 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)))).trans h_v2
  by_cases hguard : s5.vregs 3 = s5.vregs 6
  · have hok := vreg_assert_eq_run_ok 3 6 s5 hguard
    rw [hok] at hrun6; cases hrun6
    refine ⟨?_, hs5_v0, hs5_v1, hs5_v2, hs5_sail_orig⟩
    rw [hs5_v3_eq, hs5_v6] at hguard; exact hguard
  · exfalso
    have herr := vreg_assert_eq_run_err 3 6 s5 hguard
    rw [herr] at hrun6; cases hrun6

/-- Phase 5 soundness — extract the `|rem| < |adj|` (or adj=0) guard. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hp : (JoltISA.execProgram phase_remainder_bound).run js =
      .ok RETIRE_SUCCESS js₁) :
    (((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) ∧
    js₁.vregs 0 = q ∧
  js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨s1, hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 2 31 js
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2', hrun2_ex, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 3 2 4 s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3', hrun3_ex, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 3 3 4 s2
  rw [hrun3_ex] at hrun3; cases hrun3
  obtain ⟨js_afterAssert, hrun4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs 4 = adj.sshiftRight 31 := by rw [hs1_v4, h_v2]; rfl
  have hs2_v4 : s2.vregs 4 = adj.sshiftRight 31 := (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs 3 = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  have hs3_v3_eq : s3.vregs 3 = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  have hs3_v0 : s3.vregs 0 = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)).trans h_v0
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  by_cases hguard : s3.vregs 3 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 3).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 1 3 s3 hguard
    rw [hok] at hrun4; cases hrun4
    refine ⟨?_, hs3_v0, hs3_sail_orig⟩
    rcases hguard with h0 | hlt
    · left; rw [← hs3_v3_eq]; exact h0
    · right; rw [← hs3_v3_eq, ← hs3_v1]; exact hlt
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err 1 3 s3 hguard
    rw [herr] at hrun4; cases hrun4

/-- Phase 6 soundness — characterise the post-writeback Sail state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd
                 (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrunInstr, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  obtain ⟨s', hw⟩ := wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) js.sail
  have hrunConcrete :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg 0))).run js =
        .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd 0 js s' (by rw [h_v0]; exact hw)
  rw [hrunConcrete] at hrunInstr
  cases hrunInstr
  show s' = stateAfterWrite js_ref rd (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Divw

end
