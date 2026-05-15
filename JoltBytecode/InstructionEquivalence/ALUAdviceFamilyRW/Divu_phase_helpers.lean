import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_phase_helpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `divuProgram`

The 8 steps of `divuProgram` split into **five** phases (same count as
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
    (JoltISA.execInstr (.MUL (.vreg vd) (.vreg vs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then js.vregs vs1 * rs2_val
          else js.vregs r } :=
  JoltISA.mul_run_vreg_vreg_xreg vd vs1 rs2 js rs2_val hrs2

/-- Existential variant of `vreg_MUL_from_real_vs2_run`. -/
theorem vreg_MUL_from_real_vs2_run_ex
    (vd vs1 : BitVec 7) (rs2 : regidx)
    (js : SailJoltState) (rs2_val : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2_val js.sail) :
    ∃ js',
      (JoltISA.execInstr (.MUL (.vreg vd) (.vreg vs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 * rs2_val ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs vs1 * rs2_val else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_MUL_from_real_vs2_run vd vs1 rs2 js rs2_val hrs2
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
    (JoltISA.execInstr (.SUB (.vreg vd) (.xreg rs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then rs1_val - js.vregs vs2
          else js.vregs r } :=
  JoltISA.sub_run_vreg_xreg_vreg vd rs1 vs2 js rs1_val hrs1

/-- Existential variant of `vreg_SUB_from_real_vs1_run`. -/
theorem vreg_SUB_from_real_vs1_run_ex
    (vd : BitVec 7) (rs1 : regidx) (vs2 : BitVec 7)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (JoltISA.execInstr (.SUB (.vreg vd) (.xreg rs1) (.vreg vs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = rs1_val - js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then rs1_val - js.vregs vs2 else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using vreg_SUB_from_real_vs1_run vd rs1 vs2 js rs1_val hrs1
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
    (JoltISA.execInstr (.VirtualAssertMulUNoOverflow va rs)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_mulu_no_overflow_run_ok va rs js rs_val hrs hguard

/-- `vreg_assert_mulu_no_overflow va rs` — failure branch. -/
theorem vreg_assert_mulu_no_overflow_run_err
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (js.vregs va).toNat * rs_val.toNat < 2^64) :
    (JoltISA.execInstr (.VirtualAssertMulUNoOverflow va rs)).run js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js :=
  JoltISA.virtual_assert_mulu_no_overflow_run_err va rs js rs_val hrs hguard

/-- `vreg_assert_lte_real va rs` — success branch. -/
theorem vreg_assert_lte_real_run_ok
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : (js.vregs va).toNat ≤ rs_val.toNat) :
    (JoltISA.execInstr (.VirtualAssertLTEReal va rs)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_lte_real_run_ok va rs js rs_val hrs hguard

/-- `vreg_assert_lte_real va rs` — failure branch. -/
theorem vreg_assert_lte_real_run_err
    (va : BitVec 7) (rs : regidx) (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (js.vregs va).toNat ≤ rs_val.toNat) :
    (JoltISA.execInstr (.VirtualAssertLTEReal va rs)).run js =
      .error (Error.Assertion "VirtualAssertLTE") js :=
  JoltISA.virtual_assert_lte_real_run_err va rs js rs_val hrs hguard

/-- `vreg_assert_valid_unsigned_remainder_real vr rs` — success branch.
The guard `rs = 0 ∨ vr < rs` matches the Rust short-circuit on zero divisor. -/
theorem vreg_assert_valid_unsigned_remainder_real_run_ok
    (vr : BitVec 7) (rs : regidx)
    (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : rs_val = 0#64 ∨ (js.vregs vr).toNat < rs_val.toNat) :
    (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainderReal vr rs)).run js =
      .ok RETIRE_SUCCESS js :=
  JoltISA.virtual_assert_valid_unsigned_remainder_real_run_ok vr rs js rs_val hrs hguard

/-- `vreg_assert_valid_unsigned_remainder_real vr rs` — failure branch. -/
theorem vreg_assert_valid_unsigned_remainder_real_run_err
    (vr : BitVec 7) (rs : regidx)
    (js : SailJoltState) (rs_val : BitVec 64)
    (hrs : rX_bits rs js.sail = .ok rs_val js.sail)
    (hguard : ¬ (rs_val = 0#64 ∨ (js.vregs vr).toNat < rs_val.toNat)) :
    (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainderReal vr rs)).run js =
      .error
        (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
        js :=
  JoltISA.virtual_assert_valid_unsigned_remainder_real_run_err vr rs js rs_val hrs hguard

-- ============================================================================
-- Phase definitions and phase-run lemmas
-- ============================================================================

namespace Divu

/-- Phase 1 — advice load + div-by-zero assert. -/
def phase_setup (rs2 : regidx) (quotient : BitVec 64) : JoltISA.Program :=
  .instr (.VirtualAdvice 0 quotient) <|
  .instr (.VirtualAssertValidDiv0 rs2 0) <|
  .done RETIRE_SUCCESS

/-- Phase 2 — assert that `q * divisor` does not overflow 64 bits unsigned. -/
def phase_overflow_check (rs2 : regidx) : JoltISA.Program :=
  .instr (.VirtualAssertMulUNoOverflow 0 rs2) <|
  .done RETIRE_SUCCESS

/-- Phase 3 — compute `q * divisor` into v1, then assert `v1 <= rs1` unsigned. -/
def phase_quotient_product (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.MUL (.vreg 1) (.vreg 0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTEReal 1 rs1) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — compute `rs1 - q * divisor` into v1, then check the remainder bound. -/
def phase_remainder_bound (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.SUB (.vreg 1) (.xreg rs1) (.vreg 1)) <|
  .instr (.VirtualAssertValidUnsignedRemainderReal 1 rs2) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — move the quotient advice from v0 into real register rd. -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run
    (rs2 : regidx) (q : BitVec 64) (js : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs2 q)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  let s1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : BitVec 7) then q else js.vregs r }
  have h1 : (JoltISA.execInstr (.VirtualAdvice 0 q)).run js =
      .ok RETIRE_SUCCESS s1 :=
    vreg_advice_run 0 q js
  have hs1_v0 : s1.vregs 0 = q := by
    show (if (0 : BitVec 7) = 0 then q else js.vregs 0) = q
    rw [if_pos rfl]
  have hs1_sail : s1.sail = js.sail := rfl
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail := hs1_sail.symm ▸ hrs2
  have hguard_s1 : ¬ (divisor = 0#64 ∧ s1.vregs 0 ≠ (-1 : BitVec 64)) := by
    rw [hs1_v0]
    exact hguard_div0
  have h2 : (JoltISA.execInstr (.VirtualAssertValidDiv0 rs2 0)).run s1 =
      .ok RETIRE_SUCCESS s1 :=
    vreg_assert_valid_div0_run_ok rs2 0 s1 divisor hrs2_s1 hguard_s1
  refine ⟨s1, ?_, hs1_v0, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_overflow_check_run
    (rs2 : regidx) (js : SailJoltState) (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_no_overflow : q.toNat * divisor.toNat < 2^64) :
    ∃ js',
      (JoltISA.execProgram (phase_overflow_check rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  have hguard : (js.vregs 0).toNat * divisor.toNat < 2^64 := h_v0 ▸ hguard_no_overflow
  have h1 : (JoltISA.execInstr (.VirtualAssertMulUNoOverflow 0 rs2)).run js =
      .ok RETIRE_SUCCESS js :=
    vreg_assert_mulu_no_overflow_run_ok 0 rs2 js divisor hrs2 hguard
  refine ⟨js, ?_, h_v0, rfl⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js h1]
  rfl

theorem phase_quotient_product_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_lte : (q * divisor).toNat ≤ dividend.toNat) :
    ∃ js',
      (JoltISA.execProgram (phase_quotient_product rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = q * divisor ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v1, hs1_pres, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex 1 0 rs2 js divisor hrs2
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1_eq : s1.vregs 1 = q * divisor := by rw [hs1_v1, h_v0]
  have hrs1_s1 : rX_bits rs1 s1.sail = .ok dividend s1.sail := hs1_sail.symm ▸ hrs1
  have hguard : (s1.vregs 1).toNat ≤ dividend.toNat := by
    rw [hs1_v1_eq]
    exact hguard_lte
  have h2 : (JoltISA.execInstr (.VirtualAssertLTEReal 1 rs1)).run s1 =
      .ok RETIRE_SUCCESS s1 :=
    vreg_assert_lte_real_run_ok 1 rs1 s1 dividend hrs1_s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_v1_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

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
      (JoltISA.execProgram (phase_remainder_bound rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v1, hs1_pres, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex 1 rs1 1 js dividend hrs1
  have hs1_v0 : s1.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1_eq : s1.vregs 1 = dividend - q * divisor := by rw [hs1_v1, h_v1]
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail := hs1_sail.symm ▸ hrs2
  have hguard : divisor = 0#64 ∨ (s1.vregs 1).toNat < divisor.toNat := by
    rw [hs1_v1_eq]
    exact hguard_rem_bound
  have h2 : (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainderReal 1 rs2)).run s1 =
      .ok RETIRE_SUCCESS s1 :=
    vreg_assert_valid_unsigned_remainder_real_run_ok 1 rs2 s1 divisor hrs2_s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback
  have hq : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hq]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd q
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

theorem phase_setup_run_sound
    (rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (JoltISA.execProgram (phase_setup rs2 q)).run js =
      .ok RETIRE_SUCCESS js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_setup at hp
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, _hs1_pres, hs1_sail⟩ := vreg_advice_run_ex 0 q js
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hrs2_s1 : rX_bits rs2 s₁.sail = .ok divisor s₁.sail := hs1_sail.symm ▸ hrs2
  by_cases hguard : (divisor = 0#64 ∧ s₁.vregs 0 ≠ (-1 : BitVec 64))
  · exfalso
    have herr := vreg_assert_valid_div0_run_err rs2 0 s₁ divisor hrs2_s1 hguard
    rw [herr] at hrun2
    cases hrun2
  · have hok := vreg_assert_valid_div0_run_ok rs2 0 s₁ divisor hrs2_s1 hguard
    rw [hok] at hrun2
    cases hrun2
    refine ⟨?_, hs1_v0, hs1_sail⟩
    rw [hs1_v0] at hguard
    exact hguard

theorem phase_overflow_check_run_sound
    (rs2 : regidx)
    (js js₁ : SailJoltState)
    (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (JoltISA.execProgram (phase_overflow_check rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    q.toNat * divisor.toNat < 2^64 ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_overflow_check at hp
  obtain ⟨js_afterAssert, hrun1, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  by_cases hguard : (js.vregs 0).toNat * divisor.toNat < 2^64
  · have hok := vreg_assert_mulu_no_overflow_run_ok 0 rs2 js divisor hrs2 hguard
    rw [hok] at hrun1
    cases hrun1
    exact ⟨h_v0 ▸ hguard, h_v0, rfl⟩
  · exfalso
    have herr := vreg_assert_mulu_no_overflow_run_err 0 rs2 js divisor hrs2 hguard
    rw [herr] at hrun1
    cases hrun1

theorem phase_quotient_product_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (JoltISA.execProgram (phase_quotient_product rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    (q * divisor).toNat ≤ dividend.toNat ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = q * divisor ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v1, hs1_pres, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex 1 0 rs2 js divisor hrs2
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0 : s₁.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1_eq : s₁.vregs 1 = q * divisor := by rw [hs1_v1, h_v0]
  have hrs1_s1 : rX_bits rs1 s₁.sail = .ok dividend s₁.sail := hs1_sail.symm ▸ hrs1
  by_cases hguard : (s₁.vregs 1).toNat ≤ dividend.toNat
  · have hok := vreg_assert_lte_real_run_ok 1 rs1 s₁ dividend hrs1_s1 hguard
    rw [hok] at hrun2
    cases hrun2
    exact ⟨hs1_v1_eq ▸ hguard, hs1_v0, hs1_v1_eq, hs1_sail⟩
  · exfalso
    have herr := vreg_assert_lte_real_run_err 1 rs1 s₁ dividend hrs1_s1 hguard
    rw [herr] at hrun2
    cases hrun2

theorem phase_remainder_bound_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = q * divisor)
    (hp : (JoltISA.execProgram (phase_remainder_bound rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    (divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v1, hs1_pres, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex 1 rs1 1 js dividend hrs1
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0 : s₁.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1_eq : s₁.vregs 1 = dividend - q * divisor := by rw [hs1_v1, h_v1]
  have hrs2_s1 : rX_bits rs2 s₁.sail = .ok divisor s₁.sail := hs1_sail.symm ▸ hrs2
  by_cases hguard : divisor = 0#64 ∨ (s₁.vregs 1).toNat < divisor.toNat
  · have hok :=
      vreg_assert_valid_unsigned_remainder_real_run_ok 1 rs2 s₁ divisor hrs2_s1 hguard
    rw [hok] at hrun2
    cases hrun2
    refine ⟨?_, hs1_v0, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left
      exact h0
    · right
      rw [← hs1_v1_eq]
      exact hlt
  · exfalso
    have herr :=
      vreg_assert_valid_unsigned_remainder_real_run_err 1 rs2 s₁ divisor hrs2_s1 hguard
    rw [herr] at hrun2
    cases hrun2

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hq : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg 0) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hq]; exact hw)
  rw [hp_concrete] at hrun
  cases hrun
  show s' = stateAfterWrite js_ref rd q
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

end Divu

end
