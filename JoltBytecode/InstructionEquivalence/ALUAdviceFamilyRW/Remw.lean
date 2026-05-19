import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.JoltISA.Semantics.ProgramComposition
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remw_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMW: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `remwProgram`. It is the literal
21-instruction `REMW` expansion. `remwProgramPhases` is the proof-facing
decomposition used to compose the phase lemmas.
-/

namespace JoltISA

/-- Jolt ISA program for RV64 `REMW`.

The advice values are explicit oracle inputs: the 32-bit signed quotient
loaded into `v0`, and the absolute remainder loaded into `v1`.
-/
def remwProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice 0 quotient) <|
  .instr (.VirtualAdvice 1 remAbs) <|
  .instr (.VirtualSignExtendWord (.vreg 6) (.xreg rs1)) <|
  .instr (.VirtualSignExtendWord (.vreg 5) (.xreg rs2)) <|
  .instr (.VirtualAssertValidDiv0V 5 0) <|
  .instr (.VirtualChangeDivisorW 2 6 5) <|
  .instr (.VirtualSignExtendWord (.vreg 3) (.vreg 0)) <|
  .instr (.VirtualAssertEQ 3 0) <|
  sraiBlock (.vreg 4) (.vreg 1) (32 : BitVec 6) <|
  .instr (.VirtualAssertEQReal 4 (regidx.Regidx 0)) <|
  sraiBlock (.vreg 4) (.vreg 6) (31 : BitVec 6) <|
  .instr (.XOR (.vreg 5) (.vreg 1) (.vreg 4)) <|
  .instr (.SUB (.vreg 5) (.vreg 5) (.vreg 4)) <|
  .instr (.MUL (.vreg 3) (.vreg 0) (.vreg 2)) <|
  .instr (.ADD (.vreg 3) (.vreg 3) (.vreg 5)) <|
  .instr (.VirtualAssertEQ 3 6) <|
  sraiBlock (.vreg 4) (.vreg 2) (31 : BitVec 6) <|
  .instr (.XOR (.vreg 3) (.vreg 2) (.vreg 4)) <|
  .instr (.SUB (.vreg 3) (.vreg 3) (.vreg 4)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 1 3) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg 5)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `remwProgram`. -/
def remwProgramPhases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Remw.phase_setup rs1 rs2 quotient remAbs).append <|
  Remw.phase_overflow_check.append <|
  Remw.phase_rem_nonneg.append <|
  Remw.phase_quotient_product.append <|
  Remw.phase_remainder_bound.append <|
  Remw.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `remwProgram`. -/
theorem remwProgram_eq_phases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) :
    remwProgram rs2 rs1 rd quotient remAbs =
      remwProgramPhases rs2 rs1 rd quotient remAbs := by
  rfl

/-- Running `remwProgram` with honest DIVW/REMW advice succeeds and writes
Sail's signed REMW value to `rd`. -/
theorem remwProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (remwProgram rs2 rs1 rd
          (sail_divw_value dividend divisor false)
          (bv_abs (sail_remw_value dividend divisor false)))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_remw_value dividend divisor false) := by
  let q := sail_divw_value dividend divisor false
  let rem := bv_abs (sail_remw_value dividend divisor false)
  let sextDividend := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sextDivisor := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adjustedDivisor := change_divisor_w_value sextDividend sextDivisor
  let signedRem := (rem ^^^ sextDividend.sshiftRight 31) - sextDividend.sshiftRight 31

  have hguard_div0 : ¬ (sextDivisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_w dividend divisor
  have hguard_q_fits :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q :=
    hguard_q_fits_of_honest_w dividend divisor
  have hguard_rem_nonneg : shift_bits_right_arith rem (32 : BitVec 6) = 0#64 :=
    hguard_rem_nonneg_of_honest_w dividend divisor
  have hguard_quotient_product :
      q * adjustedDivisor +
          ((rem ^^^ sextDividend.sshiftRight 31) - sextDividend.sshiftRight 31) =
        sextDividend :=
    hguard_quotient_product_of_honest_w dividend divisor
  have hguard_rem_bound :
      ((adjustedDivisor ^^^ adjustedDivisor.sshiftRight 31) -
          adjustedDivisor.sshiftRight 31) = 0#64 ∨
        rem.toNat <
          ((adjustedDivisor ^^^ adjustedDivisor.sshiftRight 31) -
            adjustedDivisor.sshiftRight 31).toNat :=
    hguard_rem_bound_of_honest_w dividend divisor
  have hsigned : signedRem = sail_remw_value dividend divisor false := by
    unfold signedRem rem sextDividend
    exact signed_remw_of_honest_abs_eq_sail_remw dividend divisor

  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Remw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0

  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Remw.phase_overflow_check_run js₁ q rem adjustedDivisor sextDividend sextDivisor
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hguard_q_fits

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Remw.phase_rem_nonneg_run js₂ q rem adjustedDivisor sextDividend sextDivisor
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hguard_rem_nonneg

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v0, h4_v1, h4_v2, h4_v5, h4_sail⟩ :=
    Remw.phase_quotient_product_run js₃ q rem adjustedDivisor sextDividend sextDivisor
      h3_v0 h3_v1 h3_v2 h3_v6 hguard_quotient_product

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have h4_v5_signed : js₄.vregs 5 = signedRem := by
    unfold signedRem
    exact h4_v5
  obtain ⟨js₅, hrun5, h5_v5, h5_sail⟩ :=
    Remw.phase_remainder_bound_run js₄ rem adjustedDivisor signedRem
      h4_v1 h4_v2 h4_v5_signed hguard_rem_bound

  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  obtain ⟨js₆, hrun6, h6_sail⟩ :=
    Remw.phase_writeback_run rd js₅ js.sail signedRem h5_v5 h5_sail_orig

  have h_phase_program_succeeds :
      Program.Run (remwProgramPhases rs2 rs1 rd q rem) js js₆ := by
    unfold remwProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4
            (Program.Run.append hrun5 hrun6))))
  have h_program_succeeds :
      Program.Run (remwProgram rs2 rs1 rd q rem) js js₆ := by
    rw [remwProgram_eq_phases]
    exact h_phase_program_succeeds

  refine ⟨js₆, h_program_succeeds, ?_⟩
  rw [h6_sail, hsigned, sail_remw_value_sign_extend_roundtrip]

/-- Factoring lemma: `execute_REMW` collapses to the pure `sail_remw_value`. -/
theorem execute_REMW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_remw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REMW, sail_remw_value, bind_pure_comp]

/-- Sail's `execute_REMW ... false` writes `sail_remw_value`. -/
theorem execute_REMW_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REMW rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_remw_value dividend divisor false)) := by
  rw [execute_REMW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_remw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Honest advice makes `remwProgram` match Sail REMW. -/
theorem remwProgram_complete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (remwProgram rs2 rs1 rd
                      (sail_divw_value dividend divisor false)
                      (bv_abs (sail_remw_value dividend divisor false)))).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold remwProgram
    rw [pureWritebackTraceProgram_regidx_zero]
    rw [pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_REMW_factored rs2 rs1 (regidx.Regidx 0) false]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [hrs1, hrs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js', hjolt, hjolt_sail⟩ :=
   remwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_REMW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]

/-- Any successful REMW run writes the same Sail state as architectural
`execute_REMW ... false`. -/
theorem remwProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (remwProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor false) := by
  have h_program_succeeds : Program.Run (remwProgramPhases rs2 rs1 rd q rem) js js' := by
    rw [← remwProgram_eq_phases]
    exact hok
  unfold remwProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₅, hp5, hp6⟩ :=
    Program.Run.append_inv h_program_succeeds

  let sextDividend := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sextDivisor := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adjustedDivisor := change_divisor_w_value sextDividend sextDivisor
  let signedRem := (rem ^^^ sextDividend.sshiftRight 31) - sextDividend.sshiftRight 31

  obtain ⟨hguard1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Remw.phase_setup_run_sound rs1 rs2 q rem js js₁ dividend divisor
      hrs1 hrs2 hp1

  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Remw.phase_overflow_check_run_sound js₁ js₂ q rem adjustedDivisor
      sextDividend sextDivisor h1_v0 h1_v1 h1_v5 h1_v6 rfl hp2

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Remw.phase_rem_nonneg_run_sound js₂ js₃ q rem adjustedDivisor
      sextDividend sextDivisor h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hp3

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨hguard4, h4_v0, h4_v1, h4_v2, h4_v5, h4_sail⟩ :=
    Remw.phase_quotient_product_run_sound js₃ js₄ q rem adjustedDivisor
      sextDividend sextDivisor h3_v0 h3_v1 h3_v2 h3_v6 hp4

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have h4_v5_signed : js₄.vregs 5 = signedRem := by
    unfold signedRem
    exact h4_v5
  obtain ⟨hguard5, h5_v5, h5_sail⟩ :=
    Remw.phase_remainder_bound_run_sound js₄ js₅ rem adjustedDivisor signedRem
      h4_v1 h4_v2 h4_v5_signed hp5

  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  have hadvice :
      q = sail_divw_value dividend divisor false ∧
      rem = bv_abs (sail_remw_value dividend divisor false) :=
    advice_unique_of_guards_w dividend divisor q rem adjustedDivisor
      sextDividend sextDivisor rfl rfl rfl
      hguard1 hguard2 hguard3 hguard4 hguard5
  have hsigned : signedRem = sail_remw_value dividend divisor false := by
    unfold signedRem
    rw [hadvice.2]
    exact signed_remw_of_honest_abs_eq_sail_remw dividend divisor
  have hwrite :=
    Remw.phase_writeback_run_sound rd js₅ js' js.sail signedRem h5_v5 h5_sail_orig hp6
  rw [hsigned, sail_remw_value_sign_extend_roundtrip] at hwrite
  exact hwrite

end JoltISA

end
