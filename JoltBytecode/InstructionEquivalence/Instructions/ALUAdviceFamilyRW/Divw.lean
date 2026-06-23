import JoltBytecode.InstructionEquivalence.BundleLemmas
import JoltBytecode.JoltISA.Expansions.DivRem
import JoltBytecode.InstructionEquivalence.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.Semantics.ProgramComposition
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.DivwProgramBlocks
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Divw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVW: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divwProgram`. It is the literal
21-instruction `DIVW` expansion. `divwProgramPhases` is the proof-facing
decomposition used to compose the phase lemmas.
-/

namespace JoltISA

/-- Proof-facing phase decomposition of `divwProgram`. -/
def divwProgramPhases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Divw.phase_setup rs1 rs2 quotient remAbs).append <|
  Divw.phase_overflow_check.append <|
  Divw.phase_rem_nonneg.append <|
  Divw.phase_quotient_product.append <|
  Divw.phase_remainder_bound.append <|
  Divw.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `divwProgram`. -/
theorem divwProgram_eq_phases (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) :
    divwProgram rs2 rs1 rd quotient remAbs =
      divwProgramPhases rs2 rs1 rd quotient remAbs := by
  rfl

/-- Running `divwProgram` with honest DIVW/REMW advice succeeds and writes
Sail's signed DIVW value to `rd`. -/
theorem divwProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divwProgram rs2 rs1 rd
          (sail_divw_value dividend divisor false)
          (bv_abs (sail_remw_value dividend divisor false)))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_divw_value dividend divisor false) := by
  let q := sail_divw_value dividend divisor false
  let rem := bv_abs (sail_remw_value dividend divisor false)
  let sextDividend := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sextDivisor := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adjustedDivisor := change_divisor_w_value sextDividend sextDivisor

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

  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Divw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0

  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Divw.phase_overflow_check_run js₁ q rem adjustedDivisor sextDividend sextDivisor
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hguard_q_fits

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Divw.phase_rem_nonneg_run js₂ q rem adjustedDivisor sextDividend sextDivisor
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hguard_rem_nonneg

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v0, h4_v1, h4_v2, h4_sail⟩ :=
    Divw.phase_quotient_product_run js₃ q rem adjustedDivisor sextDividend sextDivisor
      h3_v0 h3_v1 h3_v2 h3_v6 hguard_quotient_product

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_v0, h5_sail⟩ :=
    Divw.phase_remainder_bound_run js₄ q rem adjustedDivisor
      h4_v0 h4_v1 h4_v2 hguard_rem_bound

  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  obtain ⟨js₆, hrun6, h6_sail⟩ :=
    Divw.phase_writeback_run rd js₅ js.sail q h5_v0 h5_sail_orig

  have h_phase_program_succeeds :
      Program.Run (divwProgramPhases rs2 rs1 rd q rem) js js₆ := by
    unfold divwProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4
            (Program.Run.append hrun5 hrun6))))
  have h_program_succeeds :
      Program.Run (divwProgram rs2 rs1 rd q rem) js js₆ := by
    rw [divwProgram_eq_phases]
    exact h_phase_program_succeeds

  refine ⟨js₆, h_program_succeeds, ?_⟩
  rw [h6_sail, hguard_q_fits]

/-- Factoring lemma: `execute_DIVW` collapses to the pure `sail_divw_value`. -/
theorem execute_DIVW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

/-- Sail's `execute_DIVW ... false` writes `sail_divw_value`. -/
theorem execute_DIVW_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_divw_value dividend divisor false)) := by
  rw [execute_DIVW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Any successful DIVW run pins both advice values to Sail's quotient and
absolute remainder. -/
theorem divwProgram_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divwProgram rs2 rs1 rd q rem)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_divw_value dividend divisor false ∧
    rem = bv_abs (sail_remw_value dividend divisor false) := by
  have h_program_succeeds : Program.Run (divwProgramPhases rs2 rs1 rd q rem) js js' := by
    rw [← divwProgram_eq_phases]
    exact hok
  unfold divwProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₅, hp5, _hp6⟩ :=
    Program.Run.append_inv h_program_succeeds

  let sextDividend := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sextDivisor := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adjustedDivisor := change_divisor_w_value sextDividend sextDivisor

  obtain ⟨hguard1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Divw.phase_setup_run_sound rs1 rs2 q rem js js₁ dividend divisor
      hrs1 hrs2 hp1

  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Divw.phase_overflow_check_run_sound js₁ js₂ q rem adjustedDivisor
      sextDividend sextDivisor h1_v0 h1_v1 h1_v5 h1_v6 rfl hp2

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, _, h3_v6, _⟩ :=
    Divw.phase_rem_nonneg_run_sound js₂ js₃ q rem adjustedDivisor
      sextDividend sextDivisor h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hp3

  obtain ⟨hguard4, h4_v0, h4_v1, h4_v2, _⟩ :=
    Divw.phase_quotient_product_run_sound js₃ js₄ q rem adjustedDivisor
      sextDividend sextDivisor h3_v0 h3_v1 h3_v2 h3_v6 hp4

  obtain ⟨hguard5, _, _⟩ :=
    Divw.phase_remainder_bound_run_sound js₄ js₅ q rem adjustedDivisor
      h4_v0 h4_v1 h4_v2 hp5

  exact advice_unique_of_guards_w dividend divisor q rem adjustedDivisor
    sextDividend sextDivisor rfl rfl rfl
    hguard1 hguard2 hguard3 hguard4 hguard5

end JoltISA

/-- `DIVW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem divwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.divwProgram rs2 rs1 rd quotient remAbs)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.divwProgram rs2 rs1 rd quotient remAbs) := by
    unfold JoltISA.divwProgram JoltISA.sraiBlock
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.VRegWritesNoProtectedVReg,
      Divw.a2VReg, Divw.a3VReg, Divw.t0VReg, Divw.t1VReg,
      Divw.t2VReg, Divw.t3VReg, Divw.t4VReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `DIVW` with honest advice. -/
def divwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  (quotient = sail_divw_value h.rs1_val h.rs2_val false ∧
      remAbs = bv_abs (sail_remw_value h.rs1_val h.rs2_val false)) →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.divwProgram rs2 rs1 rd quotient remAbs)).run js) =
    (execute_DIVW rs2 rs1 rd false).run js.sail

def divwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.divwProgram rs2 rs1 rd quotient remAbs)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = sail_divw_value h.rs1_val h.rs2_val false ∧
        remAbs = bv_abs (sail_remw_value h.rs1_val h.rs2_val false)

def divwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divwProgramCompletenessStatement rs2 rs1 rd quotient remAbs js h ∧
  divwProgramSoundnessStatement rs2 rs1 rd quotient remAbs js h

theorem divwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divwProgramEqSailStatement rs2 rs1 rd quotient remAbs js h := by
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
      unfold JoltISA.divwProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_DIVW_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.divwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      divwProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_divw_value dividend divisor false)
        (bv_abs (sail_remw_value dividend divisor false)) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_DIVW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_divw_value dividend divisor false) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.divwProgram_sound rs2 rs1 rd quotient remAbs js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
