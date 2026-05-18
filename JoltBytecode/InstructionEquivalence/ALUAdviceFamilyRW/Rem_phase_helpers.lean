import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_phase_helpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `remProgram`

REM shares DIV's advice, div0, overflow, and quotient-product checks.
The key difference is writeback: after reconstructing the signed
remainder in `v5`, REM preserves `v5` while computing `|adjusted
divisor|` in `v4`, then writes `v5` to `rd`.
-/

namespace Rem

/-- Phase 1 — advice loads + div-by-zero assert. Same as DIV. -/
def phase_setup (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltISA.Program :=
  Div.phase_setup rs2 quotient rem_abs

/-- Phase 2 — adjusted divisor, MULH/MUL/SRAI, overflow-check assert. Same as DIV. -/
def phase_overflow_check (rs1 rs2 : regidx) : JoltISA.Program :=
  Div.phase_overflow_check rs1 rs2

/-- Phase 3 — reconstruct signed remainder in `v5`, sum, assert equals dividend. -/
def phase_quotient_product (rs1 : regidx) : JoltISA.Program :=
  .instr (.SRAI (.vreg 3) (.xreg rs1) (63 : BitVec 6)) <|
  .instr (.XOR (.vreg 5) (.vreg 1) (.vreg 3)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 3)) <|
  .instr (.ADD (.vreg 4) (.vreg 4) (.vreg 5)) <|
  .instr (.VirtualAssertEQReal 4 rs1) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — compute `|adj_div|` into `v4`, preserving signed remainder in `v5`. -/
def phase_remainder_bound : JoltISA.Program :=
  .instr (.SRAI (.vreg 3) (.vreg 2) (63 : BitVec 6)) <|
  .instr (.XOR (.vreg 4) (.vreg 2) (.vreg 3)) <|
  .instr (.SUB (.vreg 4) (.vreg 4) (.vreg 3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 1 4) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — move the reconstructed signed remainder from `v5` into real register `rd`. -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg 5) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Phase 1 — advice loads + div-by-zero assert. -/
theorem phase_setup_run
    (rs2 : regidx) (q rem : BitVec 64) (js : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs2 q rem)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.sail = js.sail := by
  exact Div.phase_setup_run rs2 q rem js divisor hrs2 hguard_div0

/-- Phase 2 — adjusted divisor + MUL/MULH + overflow-check assert. -/
theorem phase_overflow_check_run
    (rs1 rs2 : regidx)
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63) :
    ∃ js',
      (JoltISA.execProgram (phase_overflow_check rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 4 = q * adj ∧
      js'.sail = js.sail := by
  exact Div.phase_overflow_check_run rs1 rs2 js q rem adj dividend divisor
    hrs1 hrs2 h_v0 h_v1 hadj hguard_overflow

/-- Phase 3 — signed-remainder reconstruction + `assert_eq_real v4 rs1`.

The returned `v5` value is the signed remainder that REM will write back. -/
theorem phase_quotient_product_run
    (rs1 : regidx)
    (js : SailJoltState)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hguard_quotient_product :
        q * adj +
          ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
        = dividend) :
    ∃ js',
      (JoltISA.execProgram (phase_quotient_product rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 =
        ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ :=
    vreg_SRAI_from_real_run_ex 3 rs1 63 js dividend hrs1
  obtain ⟨s2, h2, h2_v5, h2_pres, h2_sail⟩ := vreg_XOR_run_ex 5 1 3 s1
  obtain ⟨s3, h3, h3_v5, h3_pres, h3_sail⟩ := vreg_SUB_run_ex 5 5 3 s2
  obtain ⟨s4, h4, h4_v4, h4_pres, h4_sail⟩ := vreg_ADD_run_ex 4 4 5 s3
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hs1_v1 : s1.vregs 1 = rem := (h1_pres 1 (by decide)).trans h_v1
  have hs1_v3 : s1.vregs 3 = dividend.sshiftRight 63 := by rw [h1_v3]; rfl
  have hs1_v4 : s1.vregs 4 = q * adj := (h1_pres 4 (by decide)).trans h_v4
  have hs2_v3 : s2.vregs 3 = dividend.sshiftRight 63 :=
    (h2_pres 3 (by decide)).trans hs1_v3
  have hs2_v4 : s2.vregs 4 = q * adj := (h2_pres 4 (by decide)).trans hs1_v4
  have hs2_v5 : s2.vregs 5 = rem ^^^ dividend.sshiftRight 63 := by
    rw [h2_v5, hs1_v1, hs1_v3]
  have hs3_v4 : s3.vregs 4 = q * adj := (h3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5 :
      s3.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [h3_v5, hs2_v5, hs2_v3]
  have hs4_v4 : s4.vregs 4 = dividend := by
    rw [h4_v4, hs3_v4, hs3_v5]
    exact hguard_quotient_product
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail := hs4_sail.symm ▸ hrs1
  have h5 : (JoltISA.execInstr (.VirtualAssertEQReal 4 rs1)).run s4 =
      .ok RETIRE_SUCCESS s4 :=
    vreg_assert_eq_real_run_ok 4 rs1 s4 dividend hrs1_s4 hs4_v4
  have hs4_v0 : s4.vregs 0 = q :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 0 (by decide)).trans h_v0
  have hs4_v1 : s4.vregs 1 = rem :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 1 (by decide)).trans h_v1
  have hs4_v2 : s4.vregs 2 = adj :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 2 (by decide)).trans h_v2
  have hs4_v5 :
      s4.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 :=
    (h4_pres 5 (by decide)).trans hs3_v5
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_v5, hs4_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s4 h5]
  rfl

/-- Phase 4 — compute `|adj|` into `v4` and check `|rem| < |adj|`,
preserving signed remainder in `v5`. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = signedRem)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 5 = signedRem ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ := vreg_SRAI_run_ex 3 2 63 js
  obtain ⟨s2, h2, h2_v4, h2_pres, h2_sail⟩ := vreg_XOR_run_ex 4 2 3 s1
  obtain ⟨s3, h3, h3_v4, h3_pres, h3_sail⟩ := vreg_SUB_run_ex 4 4 3 s2
  have hs3_sail : s3.sail = js.sail := h3_sail.trans (h2_sail.trans h1_sail)
  have hs1_v2 : s1.vregs 2 = adj := (h1_pres 2 (by decide)).trans h_v2
  have hs1_v3 : s1.vregs 3 = adj.sshiftRight 63 := by rw [h1_v3, h_v2]; rfl
  have hs2_v3 : s2.vregs 3 = adj.sshiftRight 63 :=
    (h2_pres 3 (by decide)).trans hs1_v3
  have hs2_v4 : s2.vregs 4 = adj ^^^ adj.sshiftRight 63 := by
    rw [h2_v4, hs1_v2, hs1_v3]
  have hs3_v4 : s3.vregs 4 = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [h3_v4, hs2_v4, hs2_v3]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 h1_pres h2_pres h3_pres 1 (by decide)).trans h_v1
  have hguard_lt : s3.vregs 4 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 4).toNat := by
    rw [hs3_v1, hs3_v4]
    exact hguard_rem_bound
  have h4 : (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder 1 4)).run s3
              = .ok RETIRE_SUCCESS s3 :=
    vreg_assert_valid_unsigned_remainder_run_ok 1 4 s3 hguard_lt
  have hs3_v5 : s3.vregs 5 = signedRem :=
    (chain_pres_3 h1_pres h2_pres h3_pres 5 (by decide)).trans h_v5
  refine ⟨s3, ?_, hs3_v5, hs3_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

/-- Phase 5 — writeback `rd := v5`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs 5 = signedRem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd signedRem := by
  unfold phase_writeback
  have hrem :
      js.vregs (5 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = signedRem := by
    rw [h_v5]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd signedRem js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := vreg_ADDI_to_real_run rd 5 0 js s' (by rw [hrem]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd signedRem
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd signedRem js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness. -/
theorem phase_setup_run_sound
    (rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (JoltISA.execProgram (phase_setup rs2 q rem)).run js =
      .ok RETIRE_SUCCESS js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.sail = js.sail := by
  exact Div.phase_setup_run_sound rs2 q rem js js₁ divisor hrs2 hp

/-- Phase 2 soundness. -/
theorem phase_overflow_check_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hp : (JoltISA.execProgram (phase_overflow_check rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    mulhs q adj = (q * adj).sshiftRight 63 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 4 = q * adj ∧
    js₁.sail = js.sail := by
  exact Div.phase_overflow_check_run_sound rs1 rs2 js js₁ q rem adj
    dividend divisor hrs1 hrs2 h_v0 h_v1 hadj hp

/-- Phase 3 soundness, including the reconstructed signed remainder in `v5`. -/
theorem phase_quotient_product_run_sound
    (rs1 : regidx)
    (js js₁ : SailJoltState)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hp : (JoltISA.execProgram (phase_quotient_product rs1)).run js =
      .ok RETIRE_SUCCESS js₁) :
    q * adj +
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
      = dividend ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 =
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) ∧
  js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ :=
    vreg_SRAI_from_real_run_ex 3 rs1 63 js dividend hrs1
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 3 s1
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 3 s2
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨s4, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s4, hrun4_ex, hs4_v4, hs4_pres, hs4_sail⟩ := vreg_ADD_run_ex 4 4 5 s3
  rw [hrun4_ex] at hrun4
  cases hrun4
  obtain ⟨js_afterAssert, hrun5, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v1 : s1.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3' : s1.vregs 3 = dividend.sshiftRight 63 := by rw [hs1_v3]; rfl
  have hs1_v4 : s1.vregs 4 = q * adj := (hs1_pres 4 (by decide)).trans h_v4
  have hs2_v3 : s2.vregs 3 = dividend.sshiftRight 63 :=
    (hs2_pres 3 (by decide)).trans hs1_v3'
  have hs2_v4 : s2.vregs 4 = q * adj := (hs2_pres 4 (by decide)).trans hs1_v4
  have hs2_v5' : s2.vregs 5 = rem ^^^ dividend.sshiftRight 63 := by
    rw [hs2_v5, hs1_v1, hs1_v3']
  have hs3_v4 : s3.vregs 4 = q * adj := (hs3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5' :
      s3.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [hs3_v5, hs2_v5', hs2_v3]
  have hs4_v4' :
      s4.vregs 4 =
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) := by
    rw [hs4_v4, hs3_v4, hs3_v5']
  have hs4_sail_orig : s4.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail :=
    hs4_sail_orig.symm ▸ hrs1
  by_cases hguard : s4.vregs 4 = dividend
  · have hguard_eq :
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
          = dividend := by
      rw [← hs4_v4']
      exact hguard
    have hs4_v0 : s4.vregs 0 = q :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 0 (by decide)).trans h_v0
    have hs4_v1 : s4.vregs 1 = rem :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 1 (by decide)).trans h_v1
    have hs4_v2 : s4.vregs 2 = adj :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 2 (by decide)).trans h_v2
    have hs4_v5 :
        s4.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 :=
      (hs4_pres 5 (by decide)).trans hs3_v5'
    have hok := vreg_assert_eq_real_run_ok 4 rs1 s4 dividend hrs1_s4 hguard
    rw [hok] at hrun5
    cases hrun5
    exact ⟨hguard_eq, hs4_v0, hs4_v1, hs4_v2, hs4_v5, hs4_sail_orig⟩
  · exfalso
    have herr := vreg_assert_eq_real_run_err 4 rs1 s4 dividend hrs1_s4 hguard
    rw [herr] at hrun5
    cases hrun5

/-- Phase 4 soundness. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = signedRem)
    (hp : (JoltISA.execProgram phase_remainder_bound).run js =
      .ok RETIRE_SUCCESS js₁) :
    (((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) ∧
    js₁.vregs 5 = signedRem ∧
  js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 3 2 63 js
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v4, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 4 2 3 s1
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v4, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 4 4 3 s2
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨js_afterAssert, hrun4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3' : s1.vregs 3 = adj.sshiftRight 63 := by rw [hs1_v3, h_v2]; rfl
  have hs2_v3 : s2.vregs 3 = adj.sshiftRight 63 :=
    (hs2_pres 3 (by decide)).trans hs1_v3'
  have hs2_v4' : s2.vregs 4 = adj ^^^ adj.sshiftRight 63 := by
    rw [hs2_v4, hs1_v2, hs1_v3']
  have hs3_v4' :
      s3.vregs 4 = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [hs3_v4, hs2_v4', hs2_v3]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  have hs3_v5 : s3.vregs 5 = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 5 (by decide)).trans h_v5
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  by_cases hguard : s3.vregs 4 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 4).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 1 4 s3 hguard
    rw [hok] at hrun4
    cases hrun4
    refine ⟨?_, hs3_v5, hs3_sail_orig⟩
    rcases hguard with h0 | hlt
    · left; rw [← hs3_v4']; exact h0
    · right; rw [← hs3_v1, ← hs3_v4']; exact hlt
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err 1 4 s3 hguard
    rw [herr] at hrun4
    cases hrun4

/-- Phase 5 soundness. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs 5 = signedRem)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd signedRem := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hrem :
      js.vregs (5 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = signedRem := by
    rw [h_v5]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd signedRem js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg 5) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd 5 0 js s' (by rw [hrem]; exact hw)
  rw [hp_concrete] at hrun
  cases hrun
  show s' = stateAfterWrite js_ref rd signedRem
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd signedRem js.sail s' hw

end Rem

end
