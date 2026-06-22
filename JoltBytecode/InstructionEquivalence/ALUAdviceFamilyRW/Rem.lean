import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.MonadReduction
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Rem_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.RemProgramBlocks


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REM: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/rem.rs::inline_sequence`
at `XLEN = 64`. REM has the same guard structure as DIV, but writes the
reconstructed signed remainder rather than the quotient.
-/

namespace JoltISA

-- ----------------------------------------------------------------------------
-- Jolt REM program
-- ----------------------------------------------------------------------------

/-- New-style Jolt ISA program for RV64 `REM`. The advice values are explicit
parameters supplied by the oracle. -/
def remProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice Rem.a2VReg quotient) <|
  .instr (.VirtualAdvice Rem.a3VReg remAbs) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg Rem.a2VReg)) <|
  .instr (.VirtualChangeDivisor (.vreg Rem.t0VReg) (.xreg rs1) (.xreg rs2)) <|
  mulhBlock Div.t2VReg Div.t3VReg Div.t4VReg
    (.vreg Rem.t1VReg) (.vreg Rem.a2VReg) (.vreg Rem.t0VReg) <|
  .instr (.MUL (.vreg Rem.t2VReg) (.vreg Rem.a2VReg) (.vreg Rem.t0VReg)) <|
  sraiBlock (.vreg Rem.t3VReg) (.vreg Rem.t2VReg) (63 : BitVec 6) <|
  .instr (.VirtualAssertEQ (.vreg Rem.t1VReg) (.vreg Rem.t3VReg)) <|
  sraiBlock (.vreg Rem.t1VReg) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg Rem.t3VReg) (.vreg Rem.a3VReg) (.vreg Rem.t1VReg)) <|
  .instr (.SUB (.vreg Rem.t3VReg) (.vreg Rem.t3VReg) (.vreg Rem.t1VReg)) <|
  .instr (.ADD (.vreg Rem.t2VReg) (.vreg Rem.t2VReg) (.vreg Rem.t3VReg)) <|
  .instr (.VirtualAssertEQ (.vreg Rem.t2VReg) (.xreg rs1)) <|
  sraiBlock (.vreg Rem.t1VReg) (.vreg Rem.t0VReg) (63 : BitVec 6) <|
  .instr (.XOR (.vreg Rem.t2VReg) (.vreg Rem.t0VReg) (.vreg Rem.t1VReg)) <|
  .instr (.SUB (.vreg Rem.t2VReg) (.vreg Rem.t2VReg) (.vreg Rem.t1VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg Rem.a3VReg) (.vreg Rem.t2VReg)) <|
  .instr (.ADDI (.xreg rd) (.vreg Rem.t3VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `remProgram`. The canonical program
above remains the literal bytecode expansion. -/
def remProgramPhases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Rem.phase_setup rs2 quotient remAbs).append <|
  (Rem.phase_overflow_check rs1 rs2).append <|
  (Rem.phase_quotient_product rs1).append <|
  Rem.phase_remainder_bound.append <|
  Rem.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `remProgram`. -/
theorem remProgram_eq_phases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) :
    remProgram rs2 rs1 rd quotient remAbs =
      remProgramPhases rs2 rs1 rd quotient remAbs := by
  rfl

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `remProgram` with honest DIV/REM advice succeeds
and writes Sail's signed REM value to `rd`. -/
theorem remProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (remProgram rs2 rs1 rd
          (sail_div_value dividend divisor false)
          (bv_abs (sail_rem_value dividend divisor false)))).run js
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
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v7, h2_sail⟩ :=
    Rem.phase_overflow_check_run rs1 rs2 js₁ q rem adj dividend divisor
      hrs1_js1 hrs2_js1 h1_v0 h1_v1 rfl hguard_overflow
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v8, h3_sail⟩ :=
    Rem.phase_quotient_product_run rs1 js₂ q rem adj dividend
      hrs1_js2 h2_v0 h2_v1 h2_v2 h2_v7 hguard_quotient_product
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v8_signed : js₃.vregs Rem.t3VReg = signedRem := by
    unfold signedRem
    exact h3_v8
  obtain ⟨js₄, hrun4, h4_v8, h4_sail⟩ :=
    Rem.phase_remainder_bound_run js₃ rem adj signedRem
      h3_v1 h3_v2 h3_v8_signed hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Rem.phase_writeback_run rd js₄ js.sail signedRem h4_v8 h4_sail_orig
  have h_phase_program_succeeds :
      Program.Run (remProgramPhases rs2 rs1 rd q rem) js js₅ := by
    unfold remProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (remProgram rs2 rs1 rd q rem) js js₅ := by
    rw [remProgram_eq_phases]
    exact h_phase_program_succeeds
  rw [hsigned] at h5_sail
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_REM` collapses to the pure `sail_rem_value`. -/
theorem execute_REM_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REM, sail_rem_value, bind_pure_comp]

/-- **RHS reduction.** Sail's `execute_REM ... false` writes `sail_rem_value`. -/
theorem execute_REM_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
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

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** Any successful REM run writes the same Sail state as
architectural `execute_REM ... false`. The advice itself is not the public
statement; only the architectural writeback is. -/
theorem remProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (remProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_rem_value dividend divisor false) := by
  let adj := change_divisor_value dividend divisor
  let signedRem := (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63
  have h_program_succeeds : Program.Run (remProgramPhases rs2 rs1 rd q rem) js js' := by
    rw [← remProgram_eq_phases]
    exact hok
  unfold remProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, hp5⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨hguard1, h1_v0, h1_v1, h1_sail⟩ :=
    Rem.phase_setup_run_sound rs2 q rem js js₁ divisor hrs2 hp1
  have hrs1_1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v7, h2_sail⟩ :=
    Rem.phase_overflow_check_run_sound rs1 rs2 js₁ js₂ q rem adj dividend divisor
      hrs1_1 hrs2_1 h1_v0 h1_v1 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_v8, h3_sail⟩ :=
    Rem.phase_quotient_product_run_sound rs1 js₂ js₃ q rem adj dividend
      hrs1_2 h2_v0 h2_v1 h2_v2 h2_v7 hp3
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v8_signed : js₃.vregs Rem.t3VReg = signedRem := by
    unfold signedRem
    exact h3_v8
  obtain ⟨hguard4, h4_v8, h4_sail⟩ :=
    Rem.phase_remainder_bound_run_sound js₃ js₄ rem adj signedRem
      h3_v1 h3_v2 h3_v8_signed hp4
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
    Rem.phase_writeback_run_sound rd js₄ js' js.sail
      signedRem h4_v8 h4_sail_orig hp5
  rw [hsigned] at hwrite
  exact hwrite

end JoltISA

/-- `REM` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem remProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.remProgram rs2 rs1 rd quotient remAbs)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.remProgram rs2 rs1 rd quotient remAbs) := by
    unfold JoltISA.remProgram JoltISA.mulhBlock JoltISA.sraiBlock
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.VRegWritesNoProtectedVReg,
      Rem.a2VReg, Rem.a3VReg, Rem.t0VReg, Rem.t1VReg,
      Rem.t2VReg, Rem.t3VReg,
      Div.t2VReg, Div.t3VReg, Div.t4VReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `REM` with honest advice. -/
def remProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  (quotient = sail_div_value h.rs1_val h.rs2_val false ∧
      remAbs = bv_abs (sail_rem_value h.rs1_val h.rs2_val false)) →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.remProgram rs2 rs1 rd quotient remAbs)).run js) =
    (execute_REM rs2 rs1 rd false).run js.sail

def remProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.remProgram rs2 rs1 rd quotient remAbs)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_rem_value h.rs1_val h.rs2_val false)

def remProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remProgramCompletenessStatement rs2 rs1 rd quotient remAbs js h ∧
  remProgramSoundnessStatement rs2 rs1 rd quotient remAbs js h

theorem remProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remProgramEqSailStatement rs2 rs1 rd quotient remAbs js h := by
  constructor
  · intro hadvice
    rcases hadvice with ⟨hquotient, hremAbs⟩
    subst quotient
    subst remAbs
    let dividend := h.rs1_val
    let divisor := h.rs2_val
    have hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail := h.rs1_read
    have hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail := h.rs2_read
    have h_project_initial : System.systemProject js = js.sail := by
      simpa [project] using
        Projection.systemProject_eq_project_of_compatible js h.linkedCSRs
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      unfold JoltISA.remProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_REM_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.remProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      remProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_div_value dividend divisor false)
        (bv_abs (sail_rem_value dividend divisor false)) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_REM_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_rem_value dividend divisor false) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.remProgram_sound rs2 rs1 rd quotient remAbs js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
