import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Rem_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Rem_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REM: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/rem.rs::inline_sequence`
at `XLEN = 64`. REM has the same guard structure as DIV, but writes the
reconstructed signed remainder rather than the quotient.
-/

-- ----------------------------------------------------------------------------
-- Jolt REM inline sequence
-- ----------------------------------------------------------------------------

/-- The Jolt inline expansion of RISC-V `REM` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. -/
def jolt_rem (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                      -- VirtualAdvice v0, 0    (quotient)
  let _ ← vreg_advice 1 rem_abs                       -- VirtualAdvice v1, 0    (|remainder|)
  let _ ← vreg_assert_valid_div0 rs2 0                -- VirtualAssertValidDiv0 rs2, v0, 0
  let _ ← vreg_change_divisor 2 rs1 rs2               -- VirtualChangeDivisor   v2, rs1, rs2
  let _ ← vreg_MULH 3 0 2                             -- MULH                   v3, v0, v2
  let _ ← vreg_MUL 4 0 2                              -- MUL                    v4, v0, v2
  let _ ← vreg_SRAI 5 4 63                            -- SRAI                   v5, v4, 63
  let _ ← vreg_assert_eq 3 5                          -- VirtualAssertEQ        v3, v5, 0
  let _ ← vreg_SRAI_from_real 3 rs1 63                -- SRAI                   v3, rs1, 63
  let _ ← vreg_XOR 5 1 3                              -- XOR                    v5, v1, v3
  let _ ← vreg_SUB 5 5 3                              -- SUB                    v5, v5, v3
  let _ ← vreg_ADD 4 4 5                              -- ADD                    v4, v4, v5
  let _ ← vreg_assert_eq_real 4 rs1                   -- VirtualAssertEQ        v4, rs1, 0
  let _ ← vreg_SRAI 3 2 63                            -- SRAI                   v3, v2, 63
  let _ ← vreg_XOR 4 2 3                              -- XOR                    v4, v2, v3
  let _ ← vreg_SUB 4 4 3                              -- SUB                    v4, v4, v3
  let _ ← vreg_assert_valid_unsigned_remainder 1 4    -- VirtualAssertValidUnsignedRemainder v1, v4, 0
  vreg_ADDI_to_real rd 5 0                            -- ADDI                   rd, v5, 0   (signed remainder)

/-- `jolt_rem` as a composition of the five REM phases. -/
theorem jolt_rem_phased (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) :
    jolt_rem rs2 rs1 rd quotient rem_abs = (do
      let _ ← Rem.phase_setup rs2 quotient rem_abs
      let _ ← Rem.phase_overflow_check rs1 rs2
      let _ ← Rem.phase_quotient_product rs1
      let _ ← Rem.phase_remainder_bound
      Rem.phase_writeback rd) := by
  simp [jolt_rem, Rem.phase_setup, Rem.phase_overflow_check,
        Rem.phase_quotient_product, Rem.phase_remainder_bound,
        Rem.phase_writeback, phase_setup, phase_overflow_check, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_rem` with honest DIV/REM advice succeeds
and writes Sail's signed REM value to `rd`. -/
theorem jolt_rem_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_rem rs2 rs1 rd
          (sail_div_value dividend divisor false)
          (bv_abs (sail_rem_value dividend divisor false))).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_rem_value dividend divisor false) := by
  let q := sail_div_value dividend divisor false
  let rem := bv_abs (sail_rem_value dividend divisor false)
  let adj := change_divisor_value dividend divisor
  let signedRem := (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63
  have hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest dividend divisor
  have hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63 :=
    hguard_overflow_of_honest dividend divisor
  have hguard_quotient_product :
      q * adj +
        ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) = dividend :=
    hguard_quotient_product_of_honest dividend divisor
  have hguard_rem_bound :
      ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
        rem.toNat < ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat :=
    hguard_rem_bound_of_honest dividend divisor
  have hsigned :
      signedRem = sail_rem_value dividend divisor false := by
    unfold signedRem rem
    exact signed_rem_of_honest_abs_eq_sail_rem dividend divisor
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_sail⟩ :=
    Rem.phase_setup_run rs2 q rem js divisor hrs2 hguard_div0
  have hrs1_js1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v4, h2_sail⟩ :=
    Rem.phase_overflow_check_run rs1 rs2 js₁ q rem adj dividend divisor
      hrs1_js1 hrs2_js1 h1_v0 h1_v1 rfl hguard_overflow
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v5, h3_sail⟩ :=
    Rem.phase_quotient_product_run rs1 js₂ q rem adj dividend
      hrs1_js2 h2_v0 h2_v1 h2_v2 h2_v4 hguard_quotient_product
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v5_signed : js₃.vregs 5 = signedRem := by
    unfold signedRem
    exact h3_v5
  obtain ⟨js₄, hrun4, h4_v5, h4_sail⟩ :=
    Rem.phase_remainder_bound_run js₃ rem adj signedRem
      h3_v1 h3_v2 h3_v5_signed hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Rem.phase_writeback_run rd js₄ js.sail signedRem h4_v5 h4_sail_orig
  refine ⟨js₅, ?_, ?_⟩
  · rw [jolt_rem_phased]
    rw [bind_run_of_ok hrun1]
    rw [bind_run_of_ok hrun2]
    rw [bind_run_of_ok hrun3]
    rw [bind_run_of_ok hrun4]
    exact hrun5
  · rw [hsigned] at h5_sail
    exact h5_sail

/-- Factoring lemma: `execute_REM` collapses to the pure `sail_rem_value`. -/
theorem execute_REM_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REM, sail_rem_value, bind_pure_comp]

/-- **RHS reduction.** Sail's `execute_REM ... false` writes `sail_rem_value`. -/
theorem execute_REM_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REM rs2 rs1 rd false).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_rem_value dividend divisor false)) := by
  rw [execute_REM_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_rem_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** Honest advice makes Jolt REM match Sail REM. -/
theorem jolt_rem_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_rem rs2 rs1 rd
                      (sail_div_value dividend divisor false)
                      (bv_abs (sail_rem_value dividend divisor false))).run js) =
    (execute_REM rs2 rs1 rd false).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_rem_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_REM_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** Any successful REM run writes the same Sail state as
architectural `execute_REM ... false`. The advice itself is not the public
statement; only the architectural writeback is. -/
theorem jolt_rem_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_rem rs2 rs1 rd q rem).run js = .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_rem_value dividend divisor false) := by
  rw [jolt_rem_phased] at hok
  let adj := change_divisor_value dividend divisor
  let signedRem := (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_sail⟩ :=
    Rem.phase_setup_run_sound rs2 q rem js js₁ _ divisor hrs2 hp1
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v4, h2_sail⟩ :=
    Rem.phase_overflow_check_run_sound rs1 rs2 js₁ js₂ _ q rem adj dividend divisor
      hrs1_1 hrs2_1 h1_v0 h1_v1 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_v5, h3_sail⟩ :=
    Rem.phase_quotient_product_run_sound rs1 js₂ js₃ _ q rem adj dividend
      hrs1_2 h2_v0 h2_v1 h2_v2 h2_v4 hp3
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v5_signed : js₃.vregs 5 = signedRem := by
    unfold signedRem
    exact h3_v5
  obtain ⟨_, js₄, hp4, hp5⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard4, h4_v5, h4_sail⟩ :=
    Rem.phase_remainder_bound_run_sound js₃ js₄ _ rem adj signedRem
      h3_v1 h3_v2 h3_v5_signed hp4
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have hadvice :=
    advice_unique_of_guards dividend divisor q rem adj rfl
      hguard1 hguard2 hguard3 hguard4
  have hsigned :
      signedRem = sail_rem_value dividend divisor false := by
    unfold signedRem
    rw [hadvice.2]
    exact signed_rem_of_honest_abs_eq_sail_rem dividend divisor
  have hwrite :=
    Rem.phase_writeback_run_sound rd js₄ js' js.sail RETIRE_SUCCESS
      signedRem h4_v5 h4_sail_orig hp5
  rw [hsigned] at hwrite
  exact hwrite

end
