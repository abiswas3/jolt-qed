import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_divw`

The 21 steps of `jolt_divw` split into **six** phases (one more than
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

All phase-run lemmas are stated and sorried; each will be discharged by
unfolding its phase into the raw bind chain and walking it with
`bind_run_of_ok` + per-primitive `_run`/`_run_ex` lemmas, exactly as in
DIV's phase helpers.
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
    vreg_sign_extend_word vd vs1 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0)
          else js.vregs r } := by
  unfold vreg_sign_extend_word
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- Existential variant of `vreg_sign_extend_word_run`. -/
theorem vreg_sign_extend_word_run_ex (vd vs1 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_sign_extend_word vd vs1).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs vs1) 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_sign_extend_word
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
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
    vreg_sign_extend_word_from_real vd rs1 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)
          else js.vregs r } := by
  unfold vreg_sign_extend_word_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]

/-- Existential variant of `vreg_sign_extend_word_from_real_run`. -/
theorem vreg_sign_extend_word_from_real_run_ex
    (vd : BitVec 7) (rs1 : regidx) (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (vreg_sign_extend_word_from_real vd rs1).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = sign_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_sign_extend_word_from_real vd rs1 js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_sign_extend_word_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
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
    vreg_sign_extend_word_to_real rd vs1 js = .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } := by
  unfold vreg_sign_extend_word_to_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hwrite]

/-- `vreg_change_divisor_w vd vs1 vs2`: 32-bit version of
`vreg_change_divisor`, reading from virtual sign-extended copies.
Pure. -/
theorem vreg_change_divisor_w_run
    (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_change_divisor_w vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then change_divisor_w_value (js.vregs vs1) (js.vregs vs2)
          else js.vregs r } := by
  unfold vreg_change_divisor_w
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- Existential variant of `vreg_change_divisor_w_run`. -/
theorem vreg_change_divisor_w_run_ex
    (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_change_divisor_w vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = change_divisor_w_value (js.vregs vs1) (js.vregs vs2) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_change_divisor_w
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
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
    vreg_assert_valid_div0_v vd vq js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_valid_div0_v
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_valid_div0_v vd vq` — failure branch. -/
theorem vreg_assert_valid_div0_v_run_err
    (vd vq : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs vd = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64)) :
    vreg_assert_valid_div0_v vd vq js =
      .error
        (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
        js := by
  unfold vreg_assert_valid_div0_v
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [if_pos hguard]
  rfl

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
    JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient
  let _ ← vreg_advice 1 rem_abs
  let _ ← vreg_sign_extend_word_from_real 6 rs1
  let _ ← vreg_sign_extend_word_from_real 5 rs2
  vreg_assert_valid_div0_v 5 0

/-- Phase 2 — adjusted divisor + quotient-fits-in-32-bits check.

Computes `v2 = change_divisor_w(v6, v5)` (the `(i32::MIN, -1)` overflow
fixup at 32-bit width), then asserts that the quotient advice itself
fits in 32 bits via the round-trip `v3 = sext(v0); v3 = v0`. -/
def phase_overflow_check : JoltMonad ExecutionResult := do
  let _ ← vreg_change_divisor_w 2 6 5
  let _ ← vreg_sign_extend_word 3 0
  vreg_assert_eq 3 0

/-- Phase 3 — remainder-non-negative check (DIVW-only, no DIV analogue).

Asserts `SRAI v1 31 = x0`, which holds iff the upper 33 bits of the
`|remainder|` advice are zero — i.e. `rem_abs.toNat < 2^31`. The DIV
sequence doesn't need this because its `|rem|` is a full 64-bit value.
For DIVW the `|rem|` lives inside a 64-bit BitVec but represents a u32,
so the high half must be checked explicitly. -/
def phase_rem_nonneg : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI 4 1 31
  vreg_assert_eq_real 4 (regidx.Regidx 0)

/-- Phase 4 — reconstruct signed remainder, sum, assert equals
sign-extended dividend `v6`.

`signed_rem` is `(rem XOR sign(dividend)) - sign(dividend)` at 32-bit
width (`shamt = 31`), reading the dividend from the sign-extended
virtual copy `v6` rather than the real `rs1`. The guard then checks
`q*adj + signed_rem = sext(rs1)`. -/
def phase_quotient_product : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI 4 6 31
  let _ ← vreg_XOR 5 1 4
  let _ ← vreg_SUB 5 5 4
  let _ ← vreg_MUL 3 0 2
  let _ ← vreg_ADD 3 3 5
  vreg_assert_eq 3 6

/-- Phase 5 — compute `|adj_div|` (32-bit shamt) + `|rem| < |adj_div|` check.

Same shape as DIV's phase 4 but with `shamt = 31` instead of `63`,
operating on the virtual sign-extended adjusted divisor in `v2`. -/
def phase_remainder_bound : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI 4 2 31
  let _ ← vreg_XOR 3 2 4
  let _ ← vreg_SUB 3 3 4
  vreg_assert_valid_unsigned_remainder 1 3

/-- Phase 6 — sign-extend writeback `rd := SignExtendWord(v0)`.

Writes the validated quotient into the real destination register,
sign-extending its low 32 bits. Replaces DIV's plain `ADDI rd, v0, 0`
move because the 32-bit quotient must be sign-extended to 64 bits per
the RV64M `DIVW` spec. -/
def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_sign_extend_word_to_real rd 0

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
      (phase_setup rs1 rs2 q rem).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 5 = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.sail = js.sail := by
  sorry

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
      phase_overflow_check.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 = sext_divisor ∧
      js'.vregs 6 = sext_dividend ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 3 — DIVW-only `|rem|` ≥ 0 (as i32) check. -/
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
    (hguard_rem_nonneg : shift_bits_right_arith rem (31 : BitVec 6) = 0#64) :
    ∃ js',
      phase_rem_nonneg.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 = sext_divisor ∧
      js'.vregs 6 = sext_dividend ∧
      js'.sail = js.sail := by
  sorry

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
      phase_quotient_product.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.sail = js.sail := by
  sorry

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
      phase_remainder_bound.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 6 — sign-extend writeback `rd := SignExtendWord(v0)`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
                   (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) := by
  sorry

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction; for `jolt_divw_sound`)
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness — extract the div0 guard and post-state invariants
from a successful `phase_setup` run. -/
theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs1 rs2 q rem).run js = .ok r js₁) :
    ¬ (sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64 ∧
       q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 5 = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 6 = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 2 soundness — extract the quotient-fits-in-32 guard. -/
theorem phase_overflow_check_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hadj : adj = change_divisor_w_value sext_dividend sext_divisor)
    (hp : phase_overflow_check.run js = .ok r js₁) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 = sext_divisor ∧
    js₁.vregs 6 = sext_dividend ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 3 soundness — extract the `|rem| ≥ 0` (as i32) guard. -/
theorem phase_rem_nonneg_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = sext_divisor)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail)
    (hp : phase_rem_nonneg.run js = .ok r js₁) :
    shift_bits_right_arith rem (31 : BitVec 6) = 0#64 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 = sext_divisor ∧
    js₁.vregs 6 = sext_dividend ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 4 soundness — extract the division-equation guard. -/
theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v6 : js.vregs 6 = sext_dividend)
    (hp : phase_quotient_product.run js = .ok r js₁) :
    q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31)
      = sext_dividend ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 5 soundness — extract the `|rem| < |adj|` (or adj=0) guard. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hp : phase_remainder_bound.run js = .ok r js₁) :
    (((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 6 soundness — characterise the post-writeback Sail state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd
                 (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0)) := by
  sorry

end Divw

end
