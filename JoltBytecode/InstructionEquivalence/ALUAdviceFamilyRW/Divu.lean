import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVU: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divuProgram`. It is the literal
8-instruction `DIVU` expansion. `divuProgramPhases` is only the proof-facing
decomposition used to compose the phase lemmas.
-/

namespace JoltISA

/-- Jolt ISA program for RV64 `DIVU`. The quotient advice is explicit. -/
def divuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice Divu.v0VReg quotient) <|
  .instr (.VirtualAssertValidDiv0 rs2 Divu.v0VReg) <|
  .instr (.VirtualAssertMulUNoOverflow Divu.v0VReg rs2) <|
  .instr (.MUL (.vreg Divu.v1VReg) (.vreg Divu.v0VReg) (.xreg rs2)) <|
  .instr (.VirtualAssertLTEReal Divu.v1VReg rs1) <|
  .instr (.SUB (.vreg Divu.v1VReg) (.xreg rs1) (.vreg Divu.v1VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainderReal Divu.v1VReg rs2) <|
  .instr (.ADDI (.xreg rd) (.vreg Divu.v0VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `divuProgram`. -/
def divuProgramPhases (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Divu.phase_setup rs2 quotient).append <|
  (Divu.phase_overflow_check rs2).append <|
  (Divu.phase_quotient_product rs1 rs2).append <|
  (Divu.phase_remainder_bound rs1 rs2).append <|
  Divu.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `divuProgram`. -/
theorem divuProgram_eq_phases (rs2 rs1 rd : regidx) (quotient : BitVec 64) :
    divuProgram rs2 rs1 rd quotient = divuProgramPhases rs2 rs1 rd quotient := by
  rfl

/-- Running `divuProgram` with honest quotient advice succeeds and writes Sail's
unsigned DIV value to `rd`. -/
theorem divuProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divuProgram rs2 rs1 rd
          (sail_div_value dividend divisor true))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_div_value dividend divisor true) := by
  let q := sail_div_value dividend divisor true
  have hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_u dividend divisor
  have hguard_no_overflow : q.toNat * divisor.toNat < 2^64 :=
    hguard_no_overflow_of_honest_u dividend divisor
  have hguard_lte : (q * divisor).toNat ≤ dividend.toNat :=
    hguard_q_times_d_le_dividend_of_honest_u dividend divisor
  have hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat :=
    hguard_rem_bound_of_honest_u dividend divisor

  obtain ⟨js₁, hrun1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run rs2 q js divisor hrs2 hguard_div0

  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run rs2 js₁ q divisor
      hrs2_js1 h1_v0 hguard_no_overflow

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_js2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run rs1 rs2 js₂ q dividend divisor
      hrs1_js2 hrs2_js2 h2_v0 hguard_lte

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have hrs1_js3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_js3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    Divu.phase_remainder_bound_run rs1 rs2 js₃ q dividend divisor
      hrs1_js3 hrs2_js3 h3_v0 h3_v1 hguard_rem_bound

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divu.phase_writeback_run rd js₄ js.sail q h4_v0 h4_sail_orig

  have h_phase_program_succeeds :
      Program.Run (divuProgramPhases rs2 rs1 rd q) js js₅ := by
    unfold divuProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (divuProgram rs2 rs1 rd q) js js₅ := by
    rw [divuProgram_eq_phases]
    exact h_phase_program_succeeds
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_DIV` collapses to the pure `sail_div_value`. -/
theorem execute_DIVU_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

/-- Sail's `execute_DIV ... true` writes `sail_div_value`. -/
theorem execute_DIVU_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd true).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_div_value dividend divisor true)) := by
  rw [execute_DIVU_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Core proof that honest quotient advice makes `divuProgram` match Sail DIVU. -/
theorem divuProgram_eq_sail_core (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.divuProgram rs2 rs1 rd
                      (sail_div_value dividend divisor true))).run js) =
    (execute_DIV rs2 rs1 rd true).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold divuProgram
    rw [pureWritebackTraceProgram_regidx_zero]
    rw [pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_DIVU_factored rs2 rs1 (regidx.Regidx 0) true]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [hrs1, hrs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js', hjolt, hjolt_sail⟩ :=
   divuProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIVU_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]

/-- Any successful DIVU run pins the quotient advice to Sail's quotient. -/
theorem divuProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divuProgram rs2 rs1 rd q)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor true := by
  have h_program_succeeds : Program.Run (divuProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divuProgram_eq_phases]
    exact hok
  unfold divuProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, _hp5⟩ :=
    Program.Run.append_inv h_program_succeeds

  obtain ⟨hguard1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run_sound rs2 q js js₁ divisor hrs2 hp1

  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run_sound rs2 js₁ js₂ q divisor
      hrs2_1 h1_v0 hp2

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨hguard3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run_sound rs1 rs2 js₂ js₃ q dividend divisor
      hrs1_2 hrs2_2 h2_v0 hp3

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have hrs1_3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨hguard4, _, _⟩ :=
    Divu.phase_remainder_bound_run_sound rs1 rs2 js₃ js₄ q dividend divisor
      hrs1_3 hrs2_3 h3_v0 h3_v1 hp4

  exact advice_unique_of_guards_u dividend divisor q
    hguard1 hguard2 hguard3 hguard4

end JoltISA

/-- Main program-level equivalence for `DIVU` with honest advice. -/
theorem divuProgram_eq_sail (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.divuProgram rs2 rs1 rd
                      (sail_div_value dividend divisor true))).run js) =
    (execute_DIV rs2 rs1 rd true).run js.sail := by
  exact JoltISA.divuProgram_eq_sail_core rs2 rs1 rd js dividend divisor hrs1 hrs2

end
