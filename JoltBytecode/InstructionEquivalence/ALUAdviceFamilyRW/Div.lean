import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIV: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divProgram`. It is the literal
bytecode expansion:

1. advice loads and div-by-zero assertion,
2. adjusted divisor and overflow assertion,
3. quotient-product reconstruction assertion,
4. unsigned remainder bound assertion,
5. quotient writeback.

For the proof we also expose a phase decomposition. The proof structure mirrors
the ALU-family style: phase lemmas describe the state after each phase, the
program proof composes those phase runs, and the math lemmas discharge the
oracle guards.
-/

namespace JoltISA

/-- Jolt ISA program for RV64 `DIV`. The advice values are explicit oracle
inputs: quotient and absolute remainder. -/
def divProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice Div.a2VReg quotient) <|
  .instr (.VirtualAdvice Div.a3VReg remAbs) <|
  .instr (.VirtualAssertValidDiv0 rs2 Div.a2VReg) <|
  .instr (.VirtualChangeDivisor Div.t0VReg rs1 rs2) <|
  mulhBlock Div.t2VReg Div.t3VReg Div.t4VReg
    (.vreg Div.t1VReg) (.vreg Div.a2VReg) (.vreg Div.t0VReg) <|
  .instr (.MUL (.vreg Div.t2VReg) (.vreg Div.a2VReg) (.vreg Div.t0VReg)) <|
  sraiBlock (.vreg Div.t3VReg) (.vreg Div.t2VReg) (63 : BitVec 6) <|
  .instr (.VirtualAssertEQ Div.t1VReg Div.t3VReg) <|
  sraiBlock (.vreg Div.t1VReg) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg Div.t3VReg) (.vreg Div.a3VReg) (.vreg Div.t1VReg)) <|
  .instr (.SUB (.vreg Div.t3VReg) (.vreg Div.t3VReg) (.vreg Div.t1VReg)) <|
  .instr (.ADD (.vreg Div.t2VReg) (.vreg Div.t2VReg) (.vreg Div.t3VReg)) <|
  .instr (.VirtualAssertEQReal Div.t2VReg rs1) <|
  sraiBlock (.vreg Div.t1VReg) (.vreg Div.t0VReg) (63 : BitVec 6) <|
  .instr (.XOR (.vreg Div.t3VReg) (.vreg Div.t0VReg) (.vreg Div.t1VReg)) <|
  .instr (.SUB (.vreg Div.t3VReg) (.vreg Div.t3VReg) (.vreg Div.t1VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder Div.a3VReg Div.t3VReg) <|
  .instr (.ADDI (.xreg rd) (.vreg Div.a2VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `divProgram`. The canonical program
above remains the literal bytecode expansion. -/
def divProgramPhases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Div.phase_setup rs2 quotient remAbs).append <|
  (Div.phase_overflow_check rs1 rs2).append <|
  (Div.phase_quotient_product rs1).append <|
  Div.phase_remainder_bound.append <|
  Div.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `divProgram`. -/
theorem divProgram_eq_phases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) :
    divProgram rs2 rs1 rd quotient remAbs =
      divProgramPhases rs2 rs1 rd quotient remAbs := by
  rfl

/-- Running `divProgram` with honest DIV/REM advice succeeds and writes Sail's
signed DIV value to `rd`. -/
theorem divProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divProgram rs2 rs1 rd
          (sail_div_value dividend divisor false)
          (bv_abs (sail_rem_value dividend divisor false)))).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_div_value dividend divisor false) := by
  let q := sail_div_value dividend divisor false
  let rem := bv_abs (sail_rem_value dividend divisor false)
  let adj := change_divisor_value dividend divisor
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
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_sail⟩ :=
    Div.phase_setup_run rs2 q rem js divisor hrs2 hguard_div0
  have hrs1_js1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v7, h2_sail⟩ :=
    Div.phase_overflow_check_run rs1 rs2 js₁ q rem adj dividend divisor
      hrs1_js1 hrs2_js1 h1_v0 h1_v1 rfl hguard_overflow
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Div.phase_quotient_product_run rs1 js₂ q rem adj dividend
      hrs1_js2 h2_v0 h2_v1 h2_v2 h2_v7 hguard_quotient_product
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    Div.phase_remainder_bound_run js₃ q rem adj h3_v0 h3_v1 h3_v2 hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Div.phase_writeback_run rd js₄ js.sail q h4_v0 h4_sail_orig
  have h_phase_program_succeeds :
      Program.Run (divProgramPhases rs2 rs1 rd q rem) js js₅ := by
    unfold divProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (divProgram rs2 rs1 rd q rem) js js₅ := by
    rw [divProgram_eq_phases]
    exact h_phase_program_succeeds
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_DIV` collapses to the pure `sail_div_value`. -/
theorem execute_DIV_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

/-- Sail's `execute_DIV ... false` writes `sail_div_value`. -/
theorem execute_DIV_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd false).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_div_value dividend divisor false)) := by
  rw [execute_DIV_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Honest advice makes `divProgram` match Sail DIV. -/
theorem divProgram_complete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((execProgram (divProgram rs2 rs1 rd
                      (sail_div_value dividend divisor false)
                      (bv_abs (sail_rem_value dividend divisor false)))).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold divProgram
    rw [pureWritebackTraceProgram_regidx_zero]
    rw [pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_DIV_factored rs2 rs1 (regidx.Regidx 0) false]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [hrs1, hrs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js', hjolt, hjolt_sail⟩ :=
   divProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIV_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]

/-- Any successful DIV run pins the advice to Sail's quotient and absolute
remainder values. -/
theorem divProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor false ∧
    rem = bv_abs (sail_rem_value dividend divisor false) := by
  let adj := change_divisor_value dividend divisor
  have h_program_succeeds : Program.Run (divProgramPhases rs2 rs1 rd q rem) js js' := by
    rw [← divProgram_eq_phases]
    exact hok
  unfold divProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, _hp5⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨hguard1, h1_v0, h1_v1, h1_sail⟩ :=
    Div.phase_setup_run_sound rs2 q rem js js₁ divisor hrs2 hp1
  have hrs1_1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v7, h2_sail⟩ :=
    Div.phase_overflow_check_run_sound rs1 rs2 js₁ js₂ q rem adj dividend divisor
      hrs1_1 hrs2_1 h1_v0 h1_v1 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, _h3_sail⟩ :=
    Div.phase_quotient_product_run_sound rs1 js₂ js₃ q rem adj dividend
      hrs1_2 h2_v0 h2_v1 h2_v2 h2_v7 hp3
  obtain ⟨hguard4, _, _⟩ :=
    Div.phase_remainder_bound_run_sound js₃ js₄ q rem adj
      h3_v0 h3_v1 h3_v2 hp4
  exact advice_unique_of_guards dividend divisor q rem adj rfl
    hguard1 hguard2 hguard3 hguard4

end JoltISA

end
