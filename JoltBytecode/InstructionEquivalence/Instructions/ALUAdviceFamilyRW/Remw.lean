import JoltBytecode.InstructionEquivalence.BundleLemmas
import JoltBytecode.JoltISA.Expansions.DivRem
import JoltBytecode.InstructionEquivalence.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.Semantics.ProgramComposition
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Divw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Remw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.RemwProgramBlocks

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
  have h4_v5_signed : js₄.vregs Remw.t3VReg = signedRem := by
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
  have h4_v5_signed : js₄.vregs Remw.t3VReg = signedRem := by
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

/-- `REMW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem remwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.remwProgram rs2 rs1 rd quotient remAbs)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.remwProgram rs2 rs1 rd quotient remAbs) := by
    unfold JoltISA.remwProgram JoltISA.sraiBlock
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.VRegWritesNoProtectedVReg,
      Remw.a2VReg, Remw.a3VReg, Remw.t0VReg, Remw.t1VReg,
      Remw.t2VReg, Remw.t3VReg, Remw.t4VReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `REMW` with honest advice. -/
def remwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  (quotient = sail_divw_value h.rs1_val h.rs2_val false ∧
      remAbs = bv_abs (sail_remw_value h.rs1_val h.rs2_val false)) →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.remwProgram rs2 rs1 rd quotient remAbs)).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail

def remwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.remwProgram rs2 rs1 rd quotient remAbs)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_remw_value h.rs1_val h.rs2_val false)

def remwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remwProgramCompletenessStatement rs2 rs1 rd quotient remAbs js h ∧
  remwProgramSoundnessStatement rs2 rs1 rd quotient remAbs js h

theorem remwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remwProgramEqSailStatement rs2 rs1 rd quotient remAbs js h := by
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
      unfold JoltISA.remwProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_REMW_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.remwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      remwProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_divw_value dividend divisor false)
        (bv_abs (sail_remw_value dividend divisor false)) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_REMW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_remw_value dividend divisor false) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.remwProgram_sound rs2 rs1 rd quotient remAbs js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
