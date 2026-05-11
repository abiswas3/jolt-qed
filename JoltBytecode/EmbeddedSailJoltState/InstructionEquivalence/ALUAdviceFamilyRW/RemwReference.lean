import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Divw_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Remw_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Remw_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMW: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/remw.rs::inline_sequence`, using
the same fixed old-style remainder bound as DIVW: `SRAI rem_abs 32`,
followed by `VirtualAssertEQ` against `x0`.
-/

/-- The Jolt inline expansion of RISC-V `REMW` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. -/
def jolt_remw (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                          -- VirtualAdvice               v0, 0  (quotient)
  let _ ← vreg_advice 1 rem_abs                           -- VirtualAdvice               v1, 0  (|remainder|)
  let _ ← vreg_sign_extend_word_from_real 6 rs1           -- VirtualSignExtendWord       v6, rs1, 0
  let _ ← vreg_sign_extend_word_from_real 5 rs2           -- VirtualSignExtendWord       v5, rs2, 0
  let _ ← vreg_assert_valid_div0_v 5 0                    -- VirtualAssertValidDiv0      v5, v0, 0
  let _ ← vreg_change_divisor_w 2 6 5                     -- VirtualChangeDivisorW       v2, v6, v5
  let _ ← vreg_sign_extend_word 3 0                       -- VirtualSignExtendWord       v3, v0, 0
  let _ ← vreg_assert_eq 3 0                              -- VirtualAssertEQ             v3, v0, 0
  let _ ← vreg_SRAI 4 1 32                                -- SRAI                        v4, v1, 32
  let _ ← vreg_assert_eq_real 4 (regidx.Regidx 0)         -- VirtualAssertEQ             v4, x0, 0
  let _ ← vreg_SRAI 4 6 31                                -- SRAI                        v4, v6, 31
  let _ ← vreg_XOR 5 1 4                                  -- XOR                         v5, v1, v4
  let _ ← vreg_SUB 5 5 4                                  -- SUB                         v5, v5, v4
  let _ ← vreg_MUL 3 0 2                                  -- MUL                         v3, v0, v2
  let _ ← vreg_ADD 3 3 5                                  -- ADD                         v3, v3, v5
  let _ ← vreg_assert_eq 3 6                              -- VirtualAssertEQ             v3, v6, 0
  let _ ← vreg_SRAI 4 2 31                                -- SRAI                        v4, v2, 31
  let _ ← vreg_XOR 3 2 4                                  -- XOR                         v3, v2, v4
  let _ ← vreg_SUB 3 3 4                                  -- SUB                         v3, v3, v4
  let _ ← vreg_assert_valid_unsigned_remainder 1 3        -- VirtualAssertValidUnsignedRemainder v1, v3, 0
  vreg_sign_extend_word_to_real rd 5                      -- VirtualSignExtendWord       rd, v5, 0

theorem jolt_remw_phased (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) :
    jolt_remw rs2 rs1 rd quotient rem_abs = (do
      let _ ← Remw.phase_setup rs1 rs2 quotient rem_abs
      let _ ← Remw.phase_overflow_check
      let _ ← Remw.phase_rem_nonneg
      let _ ← Remw.phase_quotient_product
      let _ ← Remw.phase_remainder_bound
      Remw.phase_writeback rd) := by
  simp [jolt_remw, Remw.phase_setup, Remw.phase_overflow_check,
        Remw.phase_rem_nonneg, Remw.phase_quotient_product,
        Remw.phase_remainder_bound, Remw.phase_writeback,
        Divw.phase_setup, Divw.phase_overflow_check,
        Divw.phase_rem_nonneg, Divw.phase_quotient_product,
        Divw.phase_remainder_bound, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_remw` with honest DIVW/REMW advice
succeeds and writes Sail's signed REMW value to `rd`. -/
theorem jolt_remw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_remw rs2 rs1 rd
          (sail_divw_value dividend divisor false)
          (bv_abs (sail_remw_value dividend divisor false))).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_remw_value dividend divisor false) := by
  let q   := sail_divw_value dividend divisor false
  let rem := bv_abs (sail_remw_value dividend divisor false)
  let sd  := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sv  := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adj := change_divisor_w_value sd sv
  let signedRem := (rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31
  have hguard_div0 : ¬ (sv = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_w dividend divisor
  have hguard_q_fits : sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q :=
    hguard_q_fits_of_honest_w dividend divisor
  have hguard_rem_nonneg : shift_bits_right_arith rem (32 : BitVec 6) = 0#64 :=
    hguard_rem_nonneg_of_honest_w dividend divisor
  have hguard_quotient_product :
      q * adj + ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31) = sd :=
    hguard_quotient_product_of_honest_w dividend divisor
  have hguard_rem_bound :
      ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
        rem.toNat < ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat :=
    hguard_rem_bound_of_honest_w dividend divisor
  have hsigned : signedRem = sail_remw_value dividend divisor false := by
    unfold signedRem rem sd
    exact signed_remw_of_honest_abs_eq_sail_remw dividend divisor
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Remw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Remw.phase_overflow_check_run js₁ q rem adj sd sv
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hguard_q_fits
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Remw.phase_rem_nonneg_run js₂ q rem adj sd sv
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hguard_rem_nonneg
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v0, h4_v1, h4_v2, h4_v5, h4_sail⟩ :=
    Remw.phase_quotient_product_run js₃ q rem adj sd sv
      h3_v0 h3_v1 h3_v2 h3_v6 hguard_quotient_product
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have h4_v5_signed : js₄.vregs 5 = signedRem := by
    unfold signedRem
    exact h4_v5
  obtain ⟨js₅, hrun5, h5_v5, h5_sail⟩ :=
    Remw.phase_remainder_bound_run js₄ rem adj signedRem
      h4_v1 h4_v2 h4_v5_signed hguard_rem_bound
  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  obtain ⟨js₆, hrun6, h6_sail⟩ :=
    Remw.phase_writeback_run rd js₅ js.sail signedRem h5_v5 h5_sail_orig
  refine ⟨js₆, ?_, ?_⟩
  · rw [jolt_remw_phased]
    rw [bind_run_of_ok hrun1]
    rw [bind_run_of_ok hrun2]
    rw [bind_run_of_ok hrun3]
    rw [bind_run_of_ok hrun4]
    rw [bind_run_of_ok hrun5]
    exact hrun6
  · rw [h6_sail, hsigned, sail_remw_value_sign_extend_roundtrip]

/-- Factoring lemma: `execute_REMW` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_remw_value`, and a `pure RETIRE_SUCCESS`. -/
theorem execute_REMW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_remw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REMW, sail_remw_value, bind_pure_comp]

/-- **RHS reduction.** Sail's `execute_REMW ... false` writes
`sail_remw_value ... false`. -/
theorem execute_REMW_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REMW rs2 rs1 rd false).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_remw_value dividend divisor false)) := by
  rw [execute_REMW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_remw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** Honest advice makes Jolt REMW match Sail REMW. -/
theorem jolt_remw_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_remw rs2 rs1 rd
                      (sail_divw_value dividend divisor false)
                      (bv_abs (sail_remw_value dividend divisor false))).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_remw_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_REMW_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** Any successful REMW run writes the same Sail state as
architectural `execute_REMW ... false`. The raw advice is constrained by
DIVW's uniqueness lemma, but the public statement is the architectural
writeback state. -/
theorem jolt_remw_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_remw rs2 rs1 rd q rem).run js = .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor false) := by
  rw [jolt_remw_phased] at hok
  let sd  := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sv  := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adj := change_divisor_w_value sd sv
  let signedRem := (rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Remw.phase_setup_run_sound rs1 rs2 q rem js js₁ _ dividend divisor
      hrs1 hrs2 hp1
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Remw.phase_overflow_check_run_sound js₁ js₂ _ q rem adj sd sv
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Remw.phase_rem_nonneg_run_sound js₂ js₃ _ q rem adj sd sv
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hp3
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨_, js₄, hp4, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard4, h4_v0, h4_v1, h4_v2, h4_v5, h4_sail⟩ :=
    Remw.phase_quotient_product_run_sound js₃ js₄ _ q rem adj sd sv
      h3_v0 h3_v1 h3_v2 h3_v6 hp4
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have h4_v5_signed : js₄.vregs 5 = signedRem := by
    unfold signedRem
    exact h4_v5
  obtain ⟨_, js₅, hp5, hp6⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard5, h5_v5, h5_sail⟩ :=
    Remw.phase_remainder_bound_run_sound js₄ js₅ _ rem adj signedRem
      h4_v1 h4_v2 h4_v5_signed hp5
  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  have hadvice :
      q = sail_divw_value dividend divisor false ∧
      rem = bv_abs (sail_remw_value dividend divisor false) :=
    advice_unique_of_guards_w dividend divisor q rem adj sd sv rfl rfl rfl
      hguard1 hguard2 hguard3 hguard4 hguard5
  have hsigned : signedRem = sail_remw_value dividend divisor false := by
    unfold signedRem
    rw [hadvice.2]
    exact signed_remw_of_honest_abs_eq_sail_remw dividend divisor
  have hwrite :=
    Remw.phase_writeback_run_sound rd js₅ js' js.sail RETIRE_SUCCESS
      signedRem h5_v5 h5_sail_orig hp6
  rw [hsigned, sail_remw_value_sign_extend_roundtrip] at hwrite
  exact hwrite

end
