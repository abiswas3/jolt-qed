import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_divu`

The 8 steps of `jolt_divu` split into **five** phases (same count as
DIV, one fewer than DIVW). DIVU is structurally simpler than DIV
because its `|rem|` is computed *inline* (via `SUB`, in phase 4) rather
than supplied as oracle advice — so there's no `rem_abs` parameter and
no sign-fixup machinery.

This file mirrors `Div_phase_helpers.lean` and `Divw_phase_helpers.lean`
in structure and reuses the generic `_run`/`_run_ex` helpers from the
former (`vreg_advice_run_ex`, `vreg_assert_eq_run_*`, etc.). New helpers
are added for the DIVU-specific primitives
(`vreg_assert_mulu_no_overflow`, `vreg_assert_lte_real`,
`vreg_assert_valid_unsigned_remainder_real`, plus the mixed
real/virtual `vreg_MUL_from_real_vs2`, `vreg_SUB_from_real_vs1`).

Phase definitions and phase-run lemmas live in the `Divu` namespace.
-/

-- ============================================================================
-- New per-instruction `_run` lemmas (DIVU primitives)
-- ============================================================================

/-- `vreg_MUL_from_real_vs2 vd vs1 rs2`: virtual `vs1` × real `rs2` → virtual `vd`. -/
theorem vreg_MUL_from_real_vs2_run
    (vd vs1 : BitVec 7) (rs2 : regidx)
    (js : SailJoltState) (rs2_val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    vreg_MUL_from_real_vs2 vd vs1 rs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then js.vregs vs1 * rs2_val
          else js.vregs r } := by
  unfold vreg_MUL_from_real_vs2 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  rw [hrs2]

/-- Existential variant of `vreg_MUL_from_real_vs2_run`. -/
theorem vreg_MUL_from_real_vs2_run_ex
    (vd vs1 : BitVec 7) (rs2 : regidx)
    (js : SailJoltState) (rs2_val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js',
      (vreg_MUL_from_real_vs2 vd vs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 * rs2_val ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_MUL_from_real_vs2 vd vs1 rs2 js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_MUL_from_real_vs2 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  rw [hrs2]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- `vreg_SUB_from_real_vs1 vd rs1 vs2`: real `rs1` − virtual `vs2` → virtual `vd`. -/
theorem vreg_SUB_from_real_vs1_run
    (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    vreg_SUB_from_real_vs1 vd rs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then rs1_val - js.vregs vs2
          else js.vregs r } := by
  unfold vreg_SUB_from_real_vs1 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  rw [hrs1]

/-- Existential variant of `vreg_SUB_from_real_vs1_run`. -/
theorem vreg_SUB_from_real_vs1_run_ex
    (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (vreg_SUB_from_real_vs1 vd rs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = rs1_val - js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_SUB_from_real_vs1 vd rs1 vs2 js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_SUB_from_real_vs1 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  rw [hrs1]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- `vreg_assert_mulu_no_overflow va rs` — success branch. -/
theorem vreg_assert_mulu_no_overflow_run_ok
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : (js.vregs va).toNat * rs_val.toNat < 2^64) :
    vreg_assert_mulu_no_overflow va rs js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_mulu_no_overflow liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hrs]
  simp only []
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_mulu_no_overflow va rs` — failure branch. -/
theorem vreg_assert_mulu_no_overflow_run_err
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (js.vregs va).toNat * rs_val.toNat < 2^64) :
    vreg_assert_mulu_no_overflow va rs js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold vreg_assert_mulu_no_overflow liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [hrs]
  simp only []
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_lte_real va rs` — success branch. -/
theorem vreg_assert_lte_real_run_ok
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : (js.vregs va).toNat ≤ rs_val.toNat) :
    vreg_assert_lte_real va rs js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_lte_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hrs]
  simp only []
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_lte_real va rs` — failure branch. -/
theorem vreg_assert_lte_real_run_err
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (js.vregs va).toNat ≤ rs_val.toNat) :
    vreg_assert_lte_real va rs js =
      .error (Error.Assertion "VirtualAssertLTE") js := by
  unfold vreg_assert_lte_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [hrs]
  simp only []
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_valid_unsigned_remainder_real vr rs` — success branch.
The guard `rs = 0 ∨ vr < rs` matches the Rust short-circuit on zero divisor. -/
theorem vreg_assert_valid_unsigned_remainder_real_run_ok
    (vr : BitVec 7) (rs : regidx)
    (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : rs_val = 0#64 ∨ (js.vregs vr).toNat < rs_val.toNat) :
    vreg_assert_valid_unsigned_remainder_real vr rs js
      = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_valid_unsigned_remainder_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hrs]
  simp only []
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_valid_unsigned_remainder_real vr rs` — failure branch. -/
theorem vreg_assert_valid_unsigned_remainder_real_run_err
    (vr : BitVec 7) (rs : regidx)
    (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (rs_val = 0#64 ∨ (js.vregs vr).toNat < rs_val.toNat)) :
    vreg_assert_valid_unsigned_remainder_real vr rs js =
      .error
        (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
        js := by
  unfold vreg_assert_valid_unsigned_remainder_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [hrs]
  simp only []
  rw [if_neg hguard]
  rfl

-- ============================================================================
-- Phase definitions and phase-run lemmas
-- ============================================================================

namespace Divu

/-- Phase 1 — advice load + div-by-zero assert. -/
def phase_setup (rs2 : regidx) (quotient : BitVec 64) :
    JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient
  vreg_assert_valid_div0 rs2 0

/-- Phase 2 — assert that `q × divisor` does not overflow 64 bits unsigned. -/
def phase_overflow_check (rs2 : regidx) : JoltMonad ExecutionResult :=
  vreg_assert_mulu_no_overflow 0 rs2

/-- Phase 3 — compute `q × divisor` into v1, then assert `v1 ≤ rs1` (unsigned). -/
def phase_quotient_product (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_MUL_from_real_vs2 1 0 rs2
  vreg_assert_lte_real 1 rs1

/-- Phase 4 — compute `rs1 − q × divisor` into v1 (the remainder),
then assert `divisor = 0 ∨ v1 < divisor` (unsigned). -/
def phase_remainder_bound (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_SUB_from_real_vs1 1 rs1 1
  vreg_assert_valid_unsigned_remainder_real 1 rs2

/-- Phase 5 — move the quotient advice from v0 into real register rd. -/
def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_ADDI_to_real rd 0 0

-- ----------------------------------------------------------------------------
-- Phase-run lemmas (completeness side)
-- ----------------------------------------------------------------------------

/-- Phase 1 — advice load + div0 check. -/
theorem phase_setup_run
    (rs2 : regidx) (q : BitVec 64) (js : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (phase_setup rs2 q).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 2 — `q × divisor` does not overflow 64 bits unsigned. -/
theorem phase_overflow_check_run
    (rs2 : regidx) (js : SailJoltState) (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_no_overflow : q.toNat * divisor.toNat < 2^64) :
    ∃ js',
      (phase_overflow_check rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 3 — MUL produces `v1 = q*divisor`, assert `v1 ≤ dividend`. -/
theorem phase_quotient_product_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_lte : (q * divisor).toNat ≤ dividend.toNat) :
    ∃ js',
      (phase_quotient_product rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = q * divisor ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 4 — SUB produces `v1 = dividend − q*divisor`, assert
`divisor = 0 ∨ v1 < divisor`. -/
theorem phase_remainder_bound_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = q * divisor)
    (hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    ∃ js',
      (phase_remainder_bound rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 5 — writeback `rd := v0`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd q := by
  sorry

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction; for `jolt_divu_sound`)
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness — extract the div0 guard. -/
theorem phase_setup_run_sound
    (rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs2 q).run js = .ok r js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 2 soundness — extract the no-overflow guard. -/
theorem phase_overflow_check_run_sound
    (rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (phase_overflow_check rs2).run js = .ok r js₁) :
    q.toNat * divisor.toNat < 2^64 ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 3 soundness — extract the LTE guard. -/
theorem phase_quotient_product_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (phase_quotient_product rs1 rs2).run js = .ok r js₁) :
    (q * divisor).toNat ≤ dividend.toNat ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = q * divisor ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 4 soundness — extract the remainder-bound guard. -/
theorem phase_remainder_bound_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = q * divisor)
    (hp : (phase_remainder_bound rs1 rs2).run js = .ok r js₁) :
    (divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 5 soundness — characterise the post-writeback Sail state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd q := by
  sorry

end Divu

end
