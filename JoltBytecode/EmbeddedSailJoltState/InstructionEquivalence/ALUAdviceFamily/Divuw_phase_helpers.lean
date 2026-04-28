import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_phase_helpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_divuw`

The 11 steps of `jolt_divuw` split into **five** phases, ordered
slightly differently from DIVU/DIV: the div-by-zero check is at the
*end* (after the sign-extension), not the start. This is because the
DIVUW spec's div-by-zero rule is "if `divisor = 0` then `quotient =
u32::MAX`", and the assertion checks `sext(q) = -1` (i.e. `q =
u32::MAX` after sign-extension).

This file mirrors `Divu_phase_helpers.lean` and `Divw_phase_helpers.lean`
in structure. Reuses generic helpers from `Div_phase_helpers` and
DIVW-specific helpers from `Divw_phase_helpers` (which already contains
`vreg_sign_extend_word_run`, `vreg_assert_valid_div0_v_run_*`).

Phase definitions live in the `Divuw` namespace.
-/

-- ============================================================================
-- New per-instruction `_run` lemmas (DIVUW primitives)
-- ============================================================================

/-- `vreg_zero_extend_word_from_real vd rs1`: zero-extend the low 32
bits of *real* `rs1` to 64 bits, write virtual `vd`. -/
theorem vreg_zero_extend_word_from_real_run
    (vd : BitVec 7) (rs1 : regidx) (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    vreg_zero_extend_word_from_real vd rs1 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd
          then zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0)
          else js.vregs r } := by
  unfold vreg_zero_extend_word_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]

/-- Existential variant of `vreg_zero_extend_word_from_real_run`. -/
theorem vreg_zero_extend_word_from_real_run_ex
    (vd : BitVec 7) (rs1 : regidx) (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (vreg_zero_extend_word_from_real vd rs1).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = zero_extend (m := 64) (Sail.BitVec.extractLsb rs1_val 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_zero_extend_word_from_real vd rs1 js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_zero_extend_word_from_real liftSail
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

/-- `vreg_assert_mulu_no_overflow_v va vb` — success branch (virtual divisor). -/
theorem vreg_assert_mulu_no_overflow_v_run_ok
    (va vb : BitVec 7) (js : SailJoltState)
    (hguard : (js.vregs va).toNat * (js.vregs vb).toNat < 2^64) :
    vreg_assert_mulu_no_overflow_v va vb js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_mulu_no_overflow_v
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_mulu_no_overflow_v va vb` — failure branch. -/
theorem vreg_assert_mulu_no_overflow_v_run_err
    (va vb : BitVec 7) (js : SailJoltState)
    (hguard : ¬ (js.vregs va).toNat * (js.vregs vb).toNat < 2^64) :
    vreg_assert_mulu_no_overflow_v va vb js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold vreg_assert_mulu_no_overflow_v
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_lte va vb` — success branch (both virtual). -/
theorem vreg_assert_lte_run_ok
    (va vb : BitVec 7) (js : SailJoltState)
    (hguard : (js.vregs va).toNat ≤ (js.vregs vb).toNat) :
    vreg_assert_lte va vb js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_lte
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_lte va vb` — failure branch. -/
theorem vreg_assert_lte_run_err
    (va vb : BitVec 7) (js : SailJoltState)
    (hguard : ¬ (js.vregs va).toNat ≤ (js.vregs vb).toNat) :
    vreg_assert_lte va vb js =
      .error (Error.Assertion "VirtualAssertLTE") js := by
  unfold vreg_assert_lte
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [if_neg hguard]
  rfl

-- ============================================================================
-- Phase definitions and phase-run lemmas
-- ============================================================================

namespace Divuw

/-- Phase 1 — zero-extension prologue + advice + `MulUNoOverflow` check. -/
def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) :
    JoltMonad ExecutionResult := do
  let _ ← vreg_zero_extend_word_from_real 0 rs1
  let _ ← vreg_zero_extend_word_from_real 1 rs2
  let _ ← vreg_advice 2 quotient
  vreg_assert_mulu_no_overflow_v 2 1

/-- Phase 2 — `MUL v3, v2, v1` + `AssertLTE v3, v0`. -/
def phase_quotient_product : JoltMonad ExecutionResult := do
  let _ ← vreg_MUL 3 2 1
  vreg_assert_lte 3 0

/-- Phase 3 — `SUB v3, v0, v3` + `AssertValidUnsignedRemainder v3, v1`. -/
def phase_remainder_bound : JoltMonad ExecutionResult := do
  let _ ← vreg_SUB 3 0 3
  vreg_assert_valid_unsigned_remainder 3 1

/-- Phase 4 — `SignExtendWord v3, v2` + `AssertValidDiv0 v1, v3`.

Sign-extends the u32 quotient `v2` into `v3` (overwriting the
remainder), then asserts the div-by-zero special case
`zext_divisor = 0 ⇒ sext(q) = -1` (i.e. `q = u32::MAX`). -/
def phase_div0_check : JoltMonad ExecutionResult := do
  let _ ← vreg_sign_extend_word 3 2
  vreg_assert_valid_div0_v 1 3

/-- Phase 5 — writeback `rd := v3` (the sign-extended quotient). -/
def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_ADDI_to_real rd 3 0

-- ----------------------------------------------------------------------------
-- Phase-run lemmas (completeness side)
-- ----------------------------------------------------------------------------

/-- Phase 1 — zero-extension prologue + advice + no-overflow check. -/
theorem phase_setup_run
    (rs1 rs2 : regidx) (q : BitVec 64) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_no_overflow :
      q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64) :
    ∃ js',
      (phase_setup rs1 rs2 q).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs 2 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 2 — MUL + LTE check. -/
theorem phase_quotient_product_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hguard_lte : (q * zv).toNat ≤ zd.toNat) :
    ∃ js',
      phase_quotient_product.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zd ∧
      js'.vregs 1 = zv ∧
      js'.vregs 2 = q ∧
      js'.vregs 3 = q * zv ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 3 — SUB + remainder-bound check. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) :
    ∃ js',
      phase_remainder_bound.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zd ∧
      js'.vregs 1 = zv ∧
      js'.vregs 2 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 4 — sign-extend quotient into v3 + div0 check on the
sign-extended value. -/
theorem phase_div0_check_run
    (js : SailJoltState)
    (q zv : BitVec 64)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hguard_div0 :
      ¬ (zv = 0#64 ∧
         sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64))) :
    ∃ js',
      phase_div0_check.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 5 — writeback v3 to rd. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (sext_q : BitVec 64)
    (h_v3 : js.vregs 3 = sext_q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd sext_q := by
  sorry

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction)
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness — extract no-overflow guard. -/
theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs1 rs2 q).run js = .ok r js₁) :
    q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64 ∧
    js₁.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 2 soundness — extract LTE guard. -/
theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : phase_quotient_product.run js = .ok r js₁) :
    (q * zv).toNat ≤ zd.toNat ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.vregs 3 = q * zv ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 3 soundness — extract remainder-bound guard. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hp : phase_remainder_bound.run js = .ok r js₁) :
    (zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 4 soundness — extract div0 guard on the sign-extended quotient. -/
theorem phase_div0_check_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q zv : BitVec 64)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : phase_div0_check.run js = .ok r js₁) :
    ¬ (zv = 0#64 ∧
       sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 5 soundness — characterise the post-writeback Sail state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (sext_q : BitVec 64)
    (h_v3 : js.vregs 3 = sext_q)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd sext_q := by
  sorry

end Divuw

end
