import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_remw`

REMW shares DIVW's signed 32-bit advice checks. The difference is the final
writeback: after the quotient-product phase reconstructs the signed
remainder in `v5`, REMW sign-extends `v5` into the real destination.
-/

namespace Remw

def phase_setup (rs1 rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltMonad ExecutionResult :=
  Divw.phase_setup rs1 rs2 quotient rem_abs

def phase_overflow_check : JoltMonad ExecutionResult :=
  Divw.phase_overflow_check

def phase_rem_nonneg : JoltMonad ExecutionResult :=
  Divw.phase_rem_nonneg

def phase_quotient_product : JoltMonad ExecutionResult :=
  Divw.phase_quotient_product

def phase_remainder_bound : JoltMonad ExecutionResult :=
  Divw.phase_remainder_bound

def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_sign_extend_word_to_real rd 5

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
  exact Divw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0

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
  exact Divw.phase_overflow_check_run js q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v5 h_v6 hadj hguard_q_fits

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
      phase_rem_nonneg.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 5 = sext_divisor ∧
      js'.vregs 6 = sext_dividend ∧
      js'.sail = js.sail := by
  exact Divw.phase_rem_nonneg_run js q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v2 h_v5 h_v6 hx0 hguard_rem_nonneg

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
      js'.vregs 5 =
        ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product Divw.phase_quotient_product
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 6 31 js
  obtain ⟨s2, h2, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 4 s1
  obtain ⟨s3, h3, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 4 s2
  obtain ⟨s4, h4, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex 3 0 2 s3
  obtain ⟨s5, h5, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex 3 3 5 s4
  have hs5_sail_orig : s5.sail = js.sail :=
    hs5_sail.trans (hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail)))
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
  have hs5_v6 : s5.vregs 6 = sext_dividend :=
    ((hs5_pres 6 (by decide)).trans ((hs4_pres 6 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 6 (by decide)))).trans h_v6
  have hs5_v3_eq : s5.vregs 3 = q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) := by
    rw [hs5_v3, hs4_v3_eq, hs4_v5]
  have hguard : s5.vregs 3 = s5.vregs 6 := by
    rw [hs5_v3_eq, hs5_v6]
    exact hguard_quotient_product
  have h6 := vreg_assert_eq_run_ok 3 6 s5 hguard
  have hs5_v0 : s5.vregs 0 = q :=
    ((hs5_pres 0 (by decide)).trans ((hs4_pres 0 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs 1 = rem :=
    ((hs5_pres 1 (by decide)).trans ((hs4_pres 1 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs 2 = adj :=
    ((hs5_pres 2 (by decide)).trans ((hs4_pres 2 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)))).trans h_v2
  have hs5_v5 : s5.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs5_pres 5 (by decide)).trans hs4_v5
  refine ⟨s5, ?_, hs5_v0, hs5_v1, hs5_v2, hs5_v5, hs5_sail_orig⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3,
      bind_run_of_ok h4, bind_run_of_ok h5]
  exact h6

theorem phase_remainder_bound_run
    (js : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = signedRem)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) :
    ∃ js',
      phase_remainder_bound.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 5 = signedRem ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound Divw.phase_remainder_bound
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 2 31 js
  obtain ⟨s2, h2, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 3 2 4 s1
  obtain ⟨s3, h3, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 3 3 4 s2
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs 4 = adj.sshiftRight 31 := by rw [hs1_v4, h_v2]; rfl
  have hs2_v4 : s2.vregs 4 = adj.sshiftRight 31 :=
    (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs 3 = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  have hs3_v3_eq : s3.vregs 3 = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  have hguard : s3.vregs 3 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 3).toNat := by
    rw [hs3_v3_eq, hs3_v1]
    exact hguard_rem_bound
  have h4 := vreg_assert_valid_unsigned_remainder_run_ok 1 3 s3 hguard
  have hs3_v5 : s3.vregs 5 = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 5 (by decide)).trans h_v5
  refine ⟨s3, ?_, hs3_v5, hs3_sail_orig⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3]
  exact h4

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs 5 = signedRem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · show vreg_sign_extend_word_to_real rd 5 js = _
    apply vreg_sign_extend_word_to_real_run rd 5 js s'
    rw [h_v5]
    exact hw
  · show s' = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

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
  exact Divw.phase_setup_run_sound rs1 rs2 q rem js js₁ r dividend divisor hrs1 hrs2 hp

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
  exact Divw.phase_overflow_check_run_sound js js₁ r q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v5 h_v6 hadj hp

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
    shift_bits_right_arith rem (32 : BitVec 6) = 0#64 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 5 = sext_divisor ∧
    js₁.vregs 6 = sext_dividend ∧
    js₁.sail = js.sail := by
  exact Divw.phase_rem_nonneg_run_sound js js₁ r q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v2 h_v5 h_v6 hx0 hp

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
    js₁.vregs 5 =
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product Divw.phase_quotient_product at hp
  obtain ⟨_, s1, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s1', hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 6 31 js
  rw [hrun1_ex] at hrun1; cases hrun1
  obtain ⟨_, s2, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s2', hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 4 s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨_, s3, hrun3, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s3', hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 4 s2
  rw [hrun3_ex] at hrun3; cases hrun3
  obtain ⟨_, s4, hrun4, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s4', hrun4_ex, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex 3 0 2 s3
  rw [hrun4_ex] at hrun4; cases hrun4
  obtain ⟨_, s5, hrun5, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s5', hrun5_ex, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex 3 3 5 s4
  rw [hrun5_ex] at hrun5; cases hrun5
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
  have hs5_v0 : s5.vregs 0 = q :=
    ((hs5_pres 0 (by decide)).trans ((hs4_pres 0 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs 1 = rem :=
    ((hs5_pres 1 (by decide)).trans ((hs4_pres 1 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs 2 = adj :=
    ((hs5_pres 2 (by decide)).trans ((hs4_pres 2 (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres 2 (by decide)))).trans h_v2
  have hs5_v5 : s5.vregs 5 =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs5_pres 5 (by decide)).trans hs4_v5
  change vreg_assert_eq 3 6 s5 = .ok r js₁ at hp
  by_cases hguard : s5.vregs 3 = s5.vregs 6
  · have hok := vreg_assert_eq_run_ok 3 6 s5 hguard
    rw [hok] at hp
    cases hp
    refine ⟨?_, hs5_v0, hs5_v1, hs5_v2, hs5_v5, hs5_sail_orig⟩
    rw [hs5_v3_eq, hs5_v6] at hguard
    exact hguard
  · exfalso
    have herr := vreg_assert_eq_run_err 3 6 s5 hguard
    rw [herr] at hp
    cases hp

theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v5 : js.vregs 5 = signedRem)
    (hp : phase_remainder_bound.run js = .ok r js₁) :
    (((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) ∧
    js₁.vregs 5 = signedRem ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound Divw.phase_remainder_bound at hp
  obtain ⟨_, s1, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s1', hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 4 2 31 js
  rw [hrun1_ex] at hrun1; cases hrun1
  obtain ⟨_, s2, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s2', hrun2_ex, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 3 2 4 s1
  rw [hrun2_ex] at hrun2; cases hrun2
  obtain ⟨_, s3, hrun3, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s3', hrun3_ex, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 3 3 4 s2
  rw [hrun3_ex] at hrun3; cases hrun3
  have hs1_v2 : s1.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs 4 = adj.sshiftRight 31 := by rw [hs1_v4, h_v2]; rfl
  have hs2_v4 : s2.vregs 4 = adj.sshiftRight 31 :=
    (hs2_pres 4 (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs 3 = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  have hs3_v3_eq : s3.vregs 3 = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  have hs3_v5 : s3.vregs 5 = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 5 (by decide)).trans h_v5
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  change vreg_assert_valid_unsigned_remainder 1 3 s3 = .ok r js₁ at hp
  by_cases hguard : s3.vregs 3 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 3).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 1 3 s3 hguard
    rw [hok] at hp
    cases hp
    refine ⟨?_, hs3_v5, hs3_sail_orig⟩
    rcases hguard with h0 | hlt
    · left
      rw [← hs3_v3_eq]
      exact h0
    · right
      rw [← hs3_v3_eq, ← hs3_v1]
      exact hlt
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err 1 3 s3 hguard
    rw [herr] at hp
    cases hp

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs 5 = signedRem)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) := by
  unfold phase_writeback at hp
  change vreg_sign_extend_word_to_real rd 5 js = .ok r js₁ at hp
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) js.sail
  have hrun : vreg_sign_extend_word_to_real rd 5 js = .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd 5 js s' (by rw [h_v5]; exact hw)
  rw [hrun] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Remw

end
