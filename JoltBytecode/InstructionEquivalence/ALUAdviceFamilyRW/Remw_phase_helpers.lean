import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_phase_helpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `remwProgram`

REMW shares DIVW's signed 32-bit advice checks. The difference is the final
writeback: after the quotient-product phase reconstructs the signed remainder
in `v5`, REMW sign-extends `v5` into the real destination.
-/

namespace Remw

/-- Rust `a2 = allocator.allocate()`: quotient advice. -/
abbrev a2VReg : JoltISA.VReg := Divw.a2VReg

/-- Rust `a3 = allocator.allocate()`: absolute-remainder advice. -/
abbrev a3VReg : JoltISA.VReg := Divw.a3VReg

/-- Rust `t0 = allocator.allocate()`: adjusted divisor. -/
abbrev t0VReg : JoltISA.VReg := Divw.t0VReg

/-- Rust `t1 = allocator.allocate()`: temporary quotient/product check. -/
abbrev t1VReg : JoltISA.VReg := Divw.t1VReg

/-- Rust `t2 = allocator.allocate()`: shift/sign temporary. -/
abbrev t2VReg : JoltISA.VReg := Divw.t2VReg

/-- Rust `t3 = allocator.allocate()`: signed remainder, initially divisor. -/
abbrev t3VReg : JoltISA.VReg := Divw.t3VReg

/-- Rust `t4 = allocator.allocate()`: sign-extended dividend. -/
abbrev t4VReg : JoltISA.VReg := Divw.t4VReg

def phase_setup (rs1 rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltISA.Program :=
  Divw.phase_setup rs1 rs2 quotient rem_abs

def phase_overflow_check : JoltISA.Program :=
  Divw.phase_overflow_check

def phase_rem_nonneg : JoltISA.Program :=
  Divw.phase_rem_nonneg

def phase_quotient_product : JoltISA.Program :=
  Divw.phase_quotient_product

def phase_remainder_bound : JoltISA.Program :=
  Divw.phase_remainder_bound

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg t3VReg)) <|
  .done RETIRE_SUCCESS

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
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t3VReg = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs t4VReg = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.sail = js.sail := by
  exact Divw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0

theorem phase_overflow_check_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v5 : js.vregs t3VReg = sext_divisor)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hadj : adj = change_divisor_w_value sext_dividend sext_divisor)
    (hguard_q_fits :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q) :
    ∃ js',
      (JoltISA.execProgram phase_overflow_check).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t3VReg = sext_divisor ∧
      js'.vregs t4VReg = sext_dividend ∧
      js'.sail = js.sail := by
  exact Divw.phase_overflow_check_run js q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v5 h_v6 hadj hguard_q_fits

theorem phase_rem_nonneg_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v5 : js.vregs t3VReg = sext_divisor)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail)
    (hguard_rem_nonneg : shift_bits_right_arith rem (32 : BitVec 6) = 0#64) :
    ∃ js',
      (JoltISA.execProgram phase_rem_nonneg).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t3VReg = sext_divisor ∧
      js'.vregs t4VReg = sext_dividend ∧
      js'.sail = js.sail := by
  exact Divw.phase_rem_nonneg_run js q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v2 h_v5 h_v6 hx0 hguard_rem_nonneg

theorem phase_quotient_product_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hguard_quotient_product :
        q * adj +
          ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31)
        = sext_dividend) :
    ∃ js',
      (JoltISA.execProgram phase_quotient_product).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t3VReg =
        ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product Divw.phase_quotient_product
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex t2VReg t4VReg 31 js
  obtain ⟨s2, h2, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t3VReg a3VReg t2VReg s1
  obtain ⟨s3, h3, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t2VReg s2
  obtain ⟨s4, h4, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex t1VReg a2VReg t0VReg s3
  obtain ⟨s5, h5, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex t1VReg t1VReg t3VReg s4
  have hs5_sail_orig : s5.sail = js.sail :=
    hs5_sail.trans (hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail)))
  have hs1_v1 : s1.vregs a3VReg = rem := (hs1_pres a3VReg (by decide)).trans h_v1
  have hs1_v6 : s1.vregs t4VReg = sext_dividend := (hs1_pres t4VReg (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs t2VReg = sext_dividend.sshiftRight 31 := by
    rw [hs1_v4, h_v6]
    rfl
  have hs2_v4 : s2.vregs t2VReg = sext_dividend.sshiftRight 31 :=
    (hs2_pres t2VReg (by decide)).trans hs1_v4_eq
  have hs2_v5_eq : s2.vregs t3VReg = rem ^^^ sext_dividend.sshiftRight 31 := by
    rw [hs2_v5, hs1_v1, hs1_v4_eq]
  have hs3_v4 : s3.vregs t2VReg = sext_dividend.sshiftRight 31 :=
    (hs3_pres t2VReg (by decide)).trans hs2_v4
  have hs3_v5_eq : s3.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 := by
    rw [hs3_v5, hs2_v5_eq, hs2_v4]
  have hs3_v0 : s3.vregs a2VReg = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a2VReg (by decide)).trans h_v0
  have hs3_v2 : s3.vregs t0VReg = adj :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres t0VReg (by decide)).trans h_v2
  have hs4_v5 : s4.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs4_pres t3VReg (by decide)).trans hs3_v5_eq
  have hs4_v3_eq : s4.vregs t1VReg = q * adj := by
    rw [hs4_v3, hs3_v0, hs3_v2]
  have hs5_v6 : s5.vregs t4VReg = sext_dividend :=
    ((hs5_pres t4VReg (by decide)).trans ((hs4_pres t4VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres t4VReg (by decide)))).trans h_v6
  have hs5_v3_eq : s5.vregs t1VReg = q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) := by
    rw [hs5_v3, hs4_v3_eq, hs4_v5]
  have hguard : s5.vregs t1VReg = s5.vregs t4VReg := by
    rw [hs5_v3_eq, hs5_v6]
    exact hguard_quotient_product
  have h6 := vreg_assert_eq_run_ok t1VReg t4VReg s5 hguard
  have hs5_v0 : s5.vregs a2VReg = q :=
    ((hs5_pres a2VReg (by decide)).trans ((hs4_pres a2VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres a2VReg (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs a3VReg = rem :=
    ((hs5_pres a3VReg (by decide)).trans ((hs4_pres a3VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs t0VReg = adj :=
    ((hs5_pres t0VReg (by decide)).trans ((hs4_pres t0VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres t0VReg (by decide)))).trans h_v2
  have hs5_v5 : s5.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs5_pres t3VReg (by decide)).trans hs4_v5
  refine ⟨s5, ?_, hs5_v0, hs5_v1, hs5_v2, hs5_v5, hs5_sail_orig⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s5 h5]
  rw [JoltISA.execProgram_instr_run_retire _ _ s5 s5 h6]
  rfl

theorem phase_remainder_bound_run
    (js : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v5 : js.vregs t3VReg = signedRem)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs t3VReg = signedRem ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound Divw.phase_remainder_bound
  obtain ⟨s1, h1, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex t2VReg t0VReg 31 js
  obtain ⟨s2, h2, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t1VReg t0VReg t2VReg s1
  obtain ⟨s3, h3, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t1VReg t1VReg t2VReg s2
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  have hs1_v2 : s1.vregs t0VReg = adj := (hs1_pres t0VReg (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs t2VReg = adj.sshiftRight 31 := by
    rw [hs1_v4, h_v2]
    rfl
  have hs2_v4 : s2.vregs t2VReg = adj.sshiftRight 31 :=
    (hs2_pres t2VReg (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs t1VReg = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  have hs3_v3_eq : s3.vregs t1VReg = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs a3VReg = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)).trans h_v1
  have hguard : s3.vregs t1VReg = 0#64 ∨ (s3.vregs a3VReg).toNat < (s3.vregs t1VReg).toNat := by
    rw [hs3_v3_eq, hs3_v1]
    exact hguard_rem_bound
  have h4 := vreg_assert_valid_unsigned_remainder_run_ok a3VReg t1VReg s3 hguard
  have hs3_v5 : s3.vregs t3VReg = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres t3VReg (by decide)).trans h_v5
  refine ⟨s3, ?_, hs3_v5, hs3_sail_orig⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs t3VReg = signedRem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := vreg_sign_extend_word_to_real_run rd t3VReg js s' (by
      rw [h_v5]
      exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

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
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t3VReg = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs t4VReg = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.sail = js.sail := by
  exact Divw.phase_setup_run_sound rs1 rs2 q rem js js₁ dividend divisor hrs1 hrs2 hp

theorem phase_overflow_check_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v5 : js.vregs t3VReg = sext_divisor)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hadj : adj = change_divisor_w_value sext_dividend sext_divisor)
    (hp : (JoltISA.execProgram phase_overflow_check).run js =
      .ok RETIRE_SUCCESS js₁) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t0VReg = adj ∧
    js₁.vregs t3VReg = sext_divisor ∧
    js₁.vregs t4VReg = sext_dividend ∧
    js₁.sail = js.sail := by
  exact Divw.phase_overflow_check_run_sound js js₁ q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v5 h_v6 hadj hp

theorem phase_rem_nonneg_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v5 : js.vregs t3VReg = sext_divisor)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hx0 : rX_bits (regidx.Regidx 0) js.sail = .ok 0#64 js.sail)
    (hp : (JoltISA.execProgram phase_rem_nonneg).run js =
      .ok RETIRE_SUCCESS js₁) :
    shift_bits_right_arith rem (32 : BitVec 6) = 0#64 ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t0VReg = adj ∧
    js₁.vregs t3VReg = sext_divisor ∧
    js₁.vregs t4VReg = sext_dividend ∧
    js₁.sail = js.sail := by
  exact Divw.phase_rem_nonneg_run_sound js js₁ q rem adj sext_dividend sext_divisor
    h_v0 h_v1 h_v2 h_v5 h_v6 hx0 hp

theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (sext_dividend sext_divisor : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v6 : js.vregs t4VReg = sext_dividend)
    (hp : (JoltISA.execProgram phase_quotient_product).run js =
      .ok RETIRE_SUCCESS js₁) :
    q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31)
      = sext_dividend ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t0VReg = adj ∧
    js₁.vregs t3VReg =
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product Divw.phase_quotient_product at hp
  obtain ⟨s1, hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex t2VReg t4VReg 31 js
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t3VReg a3VReg t2VReg s1
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t2VReg s2
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨s4, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s4, hrun4_ex, hs4_v3, hs4_pres, hs4_sail⟩ := vreg_MUL_run_ex t1VReg a2VReg t0VReg s3
  rw [hrun4_ex] at hrun4
  cases hrun4
  obtain ⟨s5, hrun5, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s5, hrun5_ex, hs5_v3, hs5_pres, hs5_sail⟩ := vreg_ADD_run_ex t1VReg t1VReg t3VReg s4
  rw [hrun5_ex] at hrun5
  cases hrun5
  obtain ⟨js_afterAssert, hrun6, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v1 : s1.vregs a3VReg = rem := (hs1_pres a3VReg (by decide)).trans h_v1
  have hs1_v6 : s1.vregs t4VReg = sext_dividend := (hs1_pres t4VReg (by decide)).trans h_v6
  have hs1_v4_eq : s1.vregs t2VReg = sext_dividend.sshiftRight 31 := by
    rw [hs1_v4, h_v6]
    rfl
  have hs2_v4 : s2.vregs t2VReg = sext_dividend.sshiftRight 31 :=
    (hs2_pres t2VReg (by decide)).trans hs1_v4_eq
  have hs2_v5_eq : s2.vregs t3VReg = rem ^^^ sext_dividend.sshiftRight 31 := by
    rw [hs2_v5, hs1_v1, hs1_v4_eq]
  have hs3_v4 : s3.vregs t2VReg = sext_dividend.sshiftRight 31 :=
    (hs3_pres t2VReg (by decide)).trans hs2_v4
  have hs3_v5_eq : s3.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 := by
    rw [hs3_v5, hs2_v5_eq, hs2_v4]
  have hs3_v0 : s3.vregs a2VReg = q :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a2VReg (by decide)).trans h_v0
  have hs3_v2 : s3.vregs t0VReg = adj :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres t0VReg (by decide)).trans h_v2
  have hs4_v5 : s4.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs4_pres t3VReg (by decide)).trans hs3_v5_eq
  have hs4_v3_eq : s4.vregs t1VReg = q * adj := by
    rw [hs4_v3, hs3_v0, hs3_v2]
  have hs5_v3_eq : s5.vregs t1VReg = q * adj +
      ((rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31) := by
    rw [hs5_v3, hs4_v3_eq, hs4_v5]
  have hs5_v6 : s5.vregs t4VReg = sext_dividend :=
    ((hs5_pres t4VReg (by decide)).trans ((hs4_pres t4VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres t4VReg (by decide)))).trans h_v6
  have hs5_sail_orig : s5.sail = js.sail :=
    hs5_sail.trans (hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail)))
  have hs5_v0 : s5.vregs a2VReg = q :=
    ((hs5_pres a2VReg (by decide)).trans ((hs4_pres a2VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres a2VReg (by decide)))).trans h_v0
  have hs5_v1 : s5.vregs a3VReg = rem :=
    ((hs5_pres a3VReg (by decide)).trans ((hs4_pres a3VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)))).trans h_v1
  have hs5_v2 : s5.vregs t0VReg = adj :=
    ((hs5_pres t0VReg (by decide)).trans ((hs4_pres t0VReg (by decide)).trans
      (chain_pres_3 hs1_pres hs2_pres hs3_pres t0VReg (by decide)))).trans h_v2
  have hs5_v5 : s5.vregs t3VReg =
      (rem ^^^ sext_dividend.sshiftRight 31) - sext_dividend.sshiftRight 31 :=
    (hs5_pres t3VReg (by decide)).trans hs4_v5
  by_cases hguard : s5.vregs t1VReg = s5.vregs t4VReg
  · have hok := vreg_assert_eq_run_ok t1VReg t4VReg s5 hguard
    rw [hok] at hrun6
    cases hrun6
    refine ⟨?_, hs5_v0, hs5_v1, hs5_v2, hs5_v5, hs5_sail_orig⟩
    rw [hs5_v3_eq, hs5_v6] at hguard
    exact hguard
  · exfalso
    have herr := vreg_assert_eq_run_err t1VReg t4VReg s5 hguard
    rw [herr] at hrun6
    cases hrun6

theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v5 : js.vregs t3VReg = signedRem)
    (hp : (JoltISA.execProgram phase_remainder_bound).run js =
      .ok RETIRE_SUCCESS js₁) :
    (((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) ∧
    js₁.vregs t3VReg = signedRem ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound Divw.phase_remainder_bound at hp
  obtain ⟨s1, hrun1_ex, hs1_v4, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex t2VReg t0VReg 31 js
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t1VReg t0VReg t2VReg s1
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v3, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t1VReg t1VReg t2VReg s2
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨js_afterAssert, hrun4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v2 : s1.vregs t0VReg = adj := (hs1_pres t0VReg (by decide)).trans h_v2
  have hs1_v4_eq : s1.vregs t2VReg = adj.sshiftRight 31 := by
    rw [hs1_v4, h_v2]
    rfl
  have hs2_v4 : s2.vregs t2VReg = adj.sshiftRight 31 :=
    (hs2_pres t2VReg (by decide)).trans hs1_v4_eq
  have hs2_v3_eq : s2.vregs t1VReg = adj ^^^ adj.sshiftRight 31 := by
    rw [hs2_v3, hs1_v2, hs1_v4_eq]
  have hs3_v3_eq : s3.vregs t1VReg = (adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31 := by
    rw [hs3_v3, hs2_v3_eq, hs2_v4]
  have hs3_v1 : s3.vregs a3VReg = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)).trans h_v1
  have hs3_v5 : s3.vregs t3VReg = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres t3VReg (by decide)).trans h_v5
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  by_cases hguard : s3.vregs t1VReg = 0#64 ∨ (s3.vregs a3VReg).toNat < (s3.vregs t1VReg).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok a3VReg t1VReg s3 hguard
    rw [hok] at hrun4
    cases hrun4
    refine ⟨?_, hs3_v5, hs3_sail_orig⟩
    rcases hguard with h0 | hlt
    · left
      rw [← hs3_v3_eq]
      exact h0
    · right
      rw [← hs3_v3_eq, ← hs3_v1]
      exact hlt
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err a3VReg t1VReg s3 hguard
    rw [herr] at hrun4
    cases hrun4

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v5 : js.vregs t3VReg = signedRem)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrunInstr, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0)) js.sail
  have hrunConcrete :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg t3VReg))).run js =
        .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd t3VReg js s' (by rw [h_v5]; exact hw)
  rw [hrunConcrete] at hrunInstr
  cases hrunInstr
  show s' = stateAfterWrite js_ref rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb signedRem 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Remw

end
