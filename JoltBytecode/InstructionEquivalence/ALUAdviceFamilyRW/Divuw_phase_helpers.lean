import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_phase_helpers
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_phase_helpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `divuwProgram`

The 11 steps of `divuwProgram` split into **five** phases, ordered
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

namespace Divuw

/-- Phase 1 — zero-extension prologue + advice + `MulUNoOverflow` check. -/
def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) :
    JoltISA.Program :=
  .instr (.VirtualZeroExtendWord (.vreg 0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg 1) (.xreg rs2)) <|
  .instr (.VirtualAdvice 2 quotient) <|
  .instr (.VirtualAssertMulUNoOverflowV 2 1) <|
  .done RETIRE_SUCCESS

/-- Phase 2 — `MUL v3, v2, v1` + `VirtualAssertLTE v3, v0`. -/
def phase_quotient_product : JoltISA.Program :=
  .instr (.MUL (.vreg 3) (.vreg 2) (.vreg 1)) <|
  .instr (.VirtualAssertLTE 3 0) <|
  .done RETIRE_SUCCESS

/-- Phase 3 — `SUB v3, v0, v3` + `VirtualAssertValidUnsignedRemainder v3, v1`. -/
def phase_remainder_bound : JoltISA.Program :=
  .instr (.SUB (.vreg 3) (.vreg 0) (.vreg 3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 3 1) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — `SignExtendWord v3, v2` + `VirtualAssertValidDiv0 v1, v3`.

Sign-extends the u32 quotient `v2` into `v3` (overwriting the
remainder), then asserts the div-by-zero special case
`zext_divisor = 0 ⇒ sext(q) = -1` (i.e. `q = u32::MAX`). -/
def phase_div0_check : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.vreg 3) (.vreg 2)) <|
  .instr (.VirtualAssertValidDiv0V 1 3) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — writeback `rd := v3` (the sign-extended quotient). -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg 3) 0) <|
  .done RETIRE_SUCCESS

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
      (JoltISA.execProgram (phase_setup rs1 rs2 q)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs 2 = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨s1, h1, hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      0 rs1 js dividend hrs1
  obtain ⟨s2, h2, hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      1 rs2 s1 divisor (hs1_sail.symm ▸ hrs2)
  obtain ⟨s3, h3, hs3_v2, hs3_pres, hs3_sail⟩ := vreg_advice_run_ex 2 q s2
  have hs3_v0 : s3.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs3_pres 0 (by decide)).trans ((hs2_pres 0 (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) :=
    (hs3_pres 1 (by decide)).trans hs2_v1
  have hguard : (s3.vregs 2).toNat * (s3.vregs 1).toNat < 2^64 := by
    rw [hs3_v2, hs3_v1]; exact hguard_no_overflow
  have h4 := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok 2 1 s3 hguard
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  refine ⟨s3, ?_, hs3_v0, hs3_v1, hs3_v2, hs3_sail_orig⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

/-- Phase 2 — MUL + LTE check. -/
theorem phase_quotient_product_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hguard_lte : (q * zv).toNat ≤ zd.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_quotient_product).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zd ∧
      js'.vregs 1 = zv ∧
      js'.vregs 2 = q ∧
      js'.vregs 3 = q * zv ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_MUL_run_ex 3 2 1 js
  have hs1_v0 : s1.vregs 0 = zd := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = q  := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3_eq : s1.vregs 3 = q * zv := by rw [hs1_v3, h_v2, h_v1]
  have hguard : (s1.vregs 3).toNat ≤ (s1.vregs 0).toNat := by
    rw [hs1_v3_eq, hs1_v0]; exact hguard_lte
  have h2 := JoltISA.virtual_assert_lte_run_ok 3 0 s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_v1, hs1_v2, hs1_v3_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

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
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zd ∧
      js'.vregs 1 = zv ∧
      js'.vregs 2 = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SUB_run_ex 3 0 3 js
  have hs1_v0 : s1.vregs 0 = zd := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = q  := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3_eq : s1.vregs 3 = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  have hguard : s1.vregs 1 = 0#64 ∨ (s1.vregs 3).toNat < (s1.vregs 1).toNat := by
    rw [hs1_v3_eq, hs1_v1]; exact hguard_rem_bound
  have h2 := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok 3 1 s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_v1, hs1_v2, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

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
      (JoltISA.execProgram phase_div0_check).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ∧
      js'.sail = js.sail := by
  unfold phase_div0_check
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_sign_extend_word_run_ex 3 2 js
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) := by
    rw [hs1_v3, h_v2]
  have hguard : ¬ (s1.vregs 1 = 0#64 ∧ s1.vregs 3 ≠ (-1 : BitVec 64)) := by
    rw [hs1_v1, hs1_v3_eq]; exact hguard_div0
  have h2 := JoltISA.virtual_assert_valid_div0_v_run_ok 1 3 s1 hguard
  refine ⟨s1, ?_, hs1_v3_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

/-- Phase 5 — writeback v3 to rd. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (sext_q : BitVec 64)
    (h_v3 : js.vregs 3 = sext_q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd sext_q := by
  unfold phase_writeback
  have hq : js.vregs (3 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = sext_q := by
    rw [h_v3]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd sext_q js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have h1 : (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg 3) 0)).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
      vreg_ADDI_to_real_run rd 3 0 js s' (by rw [hq]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } h1]
    rfl
  · show s' = stateAfterWrite js_ref rd sext_q
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd sext_q js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction)
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness — extract no-overflow guard. -/
theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : JoltISA.Program.Run (phase_setup rs1 rs2 q) js js₁) :
    q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64 ∧
    js₁.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_setup at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      0 rs1 js dividend hrs1
  rw [hrun1_ex] at hrun1; cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ s1 js₁ hp
  obtain ⟨s2', hrun2_ex, hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      1 rs2 s1 divisor (hs1_sail.symm ▸ hrs2)
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ s2 js₁ hp
  obtain ⟨s3', hrun3_ex, hs3_v2, hs3_pres, hs3_sail⟩ := vreg_advice_run_ex 2 q s2
  rw [hrun3_ex] at hrun3; cases hrun3
  have hs3_v0 : s3.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs3_pres 0 (by decide)).trans ((hs2_pres 0 (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) :=
    (hs3_pres 1 (by decide)).trans hs2_v1
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  change (JoltISA.execProgram
      (.instr (.VirtualAssertMulUNoOverflowV 2 1) (.done RETIRE_SUCCESS))).run s3 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : (s3.vregs 2).toNat * (s3.vregs 1).toNat < 2^64
  · have hok := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok 2 1 s3 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 hok] at hp
    cases hp
    refine ⟨?_, hs3_v0, hs3_v1, hs3_v2, hs3_sail_orig⟩
    rw [hs3_v2, hs3_v1] at hguard; exact hguard
  · exfalso
    have herr := JoltISA.virtual_assert_mulu_no_overflow_v_run_err 2 1 s3 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s3 s3 _ herr] at hp
    cases hp

/-- Phase 2 soundness — extract LTE guard. -/
theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : JoltISA.Program.Run phase_quotient_product js js₁) :
    (q * zv).toNat ≤ zd.toNat ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.vregs 3 = q * zv ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_quotient_product at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_MUL_run_ex 3 2 1 js
  rw [hrun1_ex] at hrun1; cases hrun1
  have hs1_v0 : s1.vregs 0 = zd := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = q  := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3_eq : s1.vregs 3 = q * zv := by rw [hs1_v3, h_v2, h_v1]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertLTE 3 0) (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : (s1.vregs 3).toNat ≤ (s1.vregs 0).toNat
  · have hok := JoltISA.virtual_assert_lte_run_ok 3 0 s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
    cases hp
    exact ⟨hs1_v3_eq ▸ hs1_v0 ▸ hguard, hs1_v0, hs1_v1, hs1_v2, hs1_v3_eq, hs1_sail⟩
  · exfalso
    have herr := JoltISA.virtual_assert_lte_run_err 3 0 s1 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp

/-- Phase 3 soundness — extract remainder-bound guard. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hp : JoltISA.Program.Run phase_remainder_bound js js₁) :
    (zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_remainder_bound at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SUB_run_ex 3 0 3 js
  rw [hrun1_ex] at hrun1; cases hrun1
  have hs1_v0 : s1.vregs 0 = zd := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs 2 = q  := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3_eq : s1.vregs 3 = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertValidUnsignedRemainder 3 1) (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : s1.vregs 1 = 0#64 ∨ (s1.vregs 3).toNat < (s1.vregs 1).toNat
  · have hok := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok 3 1 s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
    cases hp
    refine ⟨?_, hs1_v0, hs1_v1, hs1_v2, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left; exact hs1_v1.symm.trans h0
    · right; rw [hs1_v3_eq, hs1_v1] at hlt; exact hlt
  · exfalso
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err 3 1 s1 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp

/-- Phase 4 soundness — extract div0 guard on the sign-extended quotient. -/
theorem phase_div0_check_run_sound
    (js js₁ : SailJoltState)
    (q zv : BitVec 64)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : JoltISA.Program.Run phase_div0_check js js₁) :
    ¬ (zv = 0#64 ∧
       sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_div0_check at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_sign_extend_word_run_ex 3 2 js
  rw [hrun1_ex] at hrun1; cases hrun1
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs 3 = sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) := by
    rw [hs1_v3, h_v2]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertValidDiv0V 1 3) (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : s1.vregs 1 = 0#64 ∧ s1.vregs 3 ≠ (-1 : BitVec 64)
  · exfalso
    have herr := JoltISA.virtual_assert_valid_div0_v_run_err 1 3 s1 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp
  · have hok := JoltISA.virtual_assert_valid_div0_v_run_ok 1 3 s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
    cases hp
    refine ⟨?_, hs1_v3_eq, hs1_sail⟩
    rw [hs1_v1, hs1_v3_eq] at hguard; exact hguard

/-- Phase 5 soundness — characterise the post-writeback Sail state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (sext_q : BitVec 64)
    (h_v3 : js.vregs 3 = sext_q)
    (h_sail : js.sail = js_ref)
    (hp : JoltISA.Program.Run (phase_writeback rd) js js₁) :
    js₁.sail = stateAfterWrite js_ref rd sext_q := by
  unfold JoltISA.Program.Run phase_writeback at hp
  have hq : js.vregs (3 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = sext_q := by
    rw [h_v3]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd sext_q js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg 3) 0)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd 3 0 js s' (by rw [hq]; exact hw)
  rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs }
    hp_concrete] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd sext_q
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd sext_q js.sail s' hw

end Divuw

end
