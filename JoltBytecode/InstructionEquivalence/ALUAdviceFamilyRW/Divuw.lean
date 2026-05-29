import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_phase_helpers
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVUW: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divuwProgram`. It is the
literal 11-instruction `DIVUW` expansion. `divuwProgramPhases` is only the
proof-facing decomposition used to compose the phase lemmas.
-/

namespace JoltISA

/-- Jolt ISA program for RV64 `DIVUW`. The quotient advice is explicit. -/
def divuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg 0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg 1) (.xreg rs2)) <|
  .instr (.VirtualAdvice 2 quotient) <|
  .instr (.VirtualAssertMulUNoOverflowV 2 1) <|
  .instr (.MUL (.vreg 3) (.vreg 2) (.vreg 1)) <|
  .instr (.VirtualAssertLTE 3 0) <|
  .instr (.SUB (.vreg 3) (.vreg 0) (.vreg 3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder 3 1) <|
  .instr (.VirtualSignExtendWord (.vreg 3) (.vreg 2)) <|
  .instr (.VirtualAssertValidDiv0V 1 3) <|
  .instr (.ADDI (.xreg rd) (.vreg 3) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `divuwProgram`. -/
def divuwProgramPhases (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Divuw.phase_setup rs1 rs2 quotient).append <|
  Divuw.phase_quotient_product.append <|
  Divuw.phase_remainder_bound.append <|
  Divuw.phase_div0_check.append <|
  Divuw.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `divuwProgram`. -/
theorem divuwProgram_eq_phases (rs2 rs1 rd : regidx) (quotient : BitVec 64) :
    divuwProgram rs2 rs1 rd quotient =
      divuwProgramPhases rs2 rs1 rd quotient := by
  rfl

/-- Running `divuwProgram` with honest quotient advice succeeds and writes
Sail's unsigned 32-bit DIV value to `rd`. -/
theorem divuwProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divuwProgram rs2 rs1 rd
          (sail_divuw_advice dividend divisor))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_divw_value dividend divisor true) := by
  let q := sail_divuw_advice dividend divisor
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)

  have hguard_no_overflow : q.toNat * zv.toNat < 2^64 :=
    hguard_no_overflow_of_honest_uw dividend divisor
  have hguard_lte : (q * zv).toNat ≤ zd.toNat :=
    hguard_q_times_d_le_dividend_of_honest_uw dividend divisor
  have hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat :=
    hguard_rem_bound_of_honest_uw dividend divisor
  have hguard_div0 :
      ¬ (zv = 0#64 ∧
        sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_uw dividend divisor
  have h_sext_q :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value dividend divisor

  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run rs1 rs2 q js dividend divisor
      hrs1 hrs2 hguard_no_overflow

  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run js₁ q zd zv
      h1_v0 h1_v1 h1_v2 hguard_lte

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run js₂ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hguard_rem_bound

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run js₃ q zv h3_v1 h3_v2 hguard_div0

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divuw.phase_writeback_run rd js₄ js.sail
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig

  have h_phase_program_succeeds :
      Program.Run (divuwProgramPhases rs2 rs1 rd q) js js₅ := by
    unfold divuwProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (divuwProgram rs2 rs1 rd q) js js₅ := by
    rw [divuwProgram_eq_phases]
    exact h_phase_program_succeeds
  rw [h_sext_q] at h5_sail
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_DIVW` collapses to the pure `sail_divw_value`. -/
theorem execute_DIVUW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

/-- Sail's `execute_DIVW ... true` writes `sail_divw_value`. -/
theorem execute_DIVUW_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd true).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_divw_value dividend divisor true)) := by
  rw [execute_DIVUW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Honest quotient advice makes `divuwProgram` match Sail DIVUW. -/
theorem divuwProgram_complete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (divuwProgram rs2 rs1 rd
                      (sail_divuw_advice dividend divisor))).run js) =
    (execute_DIVW rs2 rs1 rd true).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold divuwProgram
    rw [pureWritebackTraceProgram_regidx_zero]
    rw [pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_DIVUW_factored rs2 rs1 (regidx.Regidx 0) true]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [hrs1, hrs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js', hjolt, hjolt_sail⟩ :=
   divuwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIVUW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]

/-- Any successful DIVUW run writes Sail's unsigned 32-bit quotient. -/
theorem divuwProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divuwProgram rs2 rs1 rd q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_divw_value dividend divisor true) := by
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  have h_program_succeeds : Program.Run (divuwProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divuwProgram_eq_phases]
    exact hok
  unfold divuwProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, hp5⟩ :=
    Program.Run.append_inv h_program_succeeds

  obtain ⟨hguard1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run_sound rs1 rs2 q js js₁ dividend divisor
      hrs1 hrs2 hp1

  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run_sound js₁ js₂ q zd zv
      h1_v0 h1_v1 h1_v2 hp2

  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run_sound js₂ js₃ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hp3

  obtain ⟨hguard4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run_sound js₃ js₄ q zv
      h3_v1 h3_v2 hp4

  have h_sext :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value_of_guards_uw dividend divisor q
      hguard1 hguard2 hguard3 hguard4
  have h4_sail_orig : js₄.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hwrite :=
    Divuw.phase_writeback_run_sound rd js₄ js' js.sail
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig hp5
  rw [h_sext] at hwrite
  exact hwrite

end JoltISA

end
