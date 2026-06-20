import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMUW: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `remuwProgram`. It is the
literal 9-instruction `REMUW` expansion. `remuwProgramPhases` is only the
proof-facing decomposition used to compose the phase lemmas.
-/

namespace JoltISA

/-- Jolt ISA program for RV64 `REMUW`. The quotient advice is explicit. -/
def remuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg Remuw.rs1VReg) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg Remuw.rs2VReg) (.xreg rs2)) <|
  .instr (.VirtualAdvice Remuw.vTmpVReg quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg Remuw.vTmpVReg) (.vreg Remuw.rs2VReg)) <|
  .instr (.MUL (.vreg Remuw.vTmpVReg) (.vreg Remuw.vTmpVReg) (.vreg Remuw.rs2VReg)) <|
  .instr (.VirtualAssertLTE (.vreg Remuw.tempVReg) (.vreg Remuw.rs1VReg)) <|
  .instr (.SUB (.vreg Remuw.vTmpVReg) (.vreg Remuw.rs1VReg) (.vreg Remuw.vTmpVReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg Remuw.vTmpVReg) (.vreg Remuw.rs2VReg)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg Remuw.vTmpVReg)) <|
  .done RETIRE_SUCCESS

/-- Proof-facing phase decomposition of `remuwProgram`. -/
def remuwProgramPhases (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Remuw.phase_setup rs1 rs2 quotient).append <|
  Remuw.phase_quotient_product.append <|
  Remuw.phase_remainder_bound.append <|
  Remuw.phase_writeback rd

/-- The phase decomposition is definitionally the same bytecode as `remuwProgram`. -/
theorem remuwProgram_eq_phases (rs2 rs1 rd : regidx) (quotient : BitVec 64) :
    remuwProgram rs2 rs1 rd quotient =
      remuwProgramPhases rs2 rs1 rd quotient := by
  rfl

/-- Running `remuwProgram` with honest quotient advice succeeds and writes
Sail's unsigned 32-bit REM value to `rd`. -/
theorem remuwProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (remuwProgram rs2 rs1 rd
          (sail_divuw_advice dividend divisor))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_remw_value dividend divisor true) := by
  let q := sail_divuw_advice dividend divisor
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let rem := zd - q * zv

  have hguard_no_overflow : q.toNat * zv.toNat < 2^64 :=
    hguard_no_overflow_of_honest_uw dividend divisor
  have hguard_lte : (q * zv).toNat ≤ zd.toNat :=
    hguard_q_times_d_le_dividend_of_honest_uw dividend divisor
  have hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat :=
    hguard_rem_bound_of_honest_uw dividend divisor
  have hrem :
      sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0) =
        sail_remw_value dividend divisor true := by
    unfold rem
    exact signExtend_remainder_eq_sail_remw_of_guards_uw dividend divisor q
      hguard_no_overflow hguard_lte hguard_rem_bound

  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remuw.phase_setup_run rs1 rs2 q js dividend divisor
      hrs1 hrs2 hguard_no_overflow

  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v3, h2_sail⟩ :=
    Remuw.phase_quotient_product_run js₁ q zd zv
      h1_v0 h1_v1 h1_v2 hguard_lte

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨js₃, hrun3, h3_v3, h3_sail⟩ :=
    Remuw.phase_remainder_bound_run js₂ q zd zv
      h2_v0 h2_v1 h2_v3 hguard_rem_bound

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v3_rem : js₃.vregs Remuw.tempVReg = rem := by
    unfold rem
    exact h3_v3
  obtain ⟨js₄, hrun4, h4_sail⟩ :=
    Remuw.phase_writeback_run rd js₃ js.sail rem h3_v3_rem h3_sail_orig

  have h_phase_program_succeeds :
      Program.Run (remuwProgramPhases rs2 rs1 rd q) js js₄ := by
    unfold remuwProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3 hrun4))
  have h_program_succeeds :
      Program.Run (remuwProgram rs2 rs1 rd q) js js₄ := by
    rw [remuwProgram_eq_phases]
    exact h_phase_program_succeeds
  rw [hrem] at h4_sail
  exact ⟨js₄, h_program_succeeds, h4_sail⟩

/-- Factoring lemma: `execute_REMW` collapses to the pure `sail_remw_value`. -/
theorem execute_REMUW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_remw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REMW, sail_remw_value, bind_pure_comp]

/-- Sail's `execute_REMW ... true` writes `sail_remw_value`. -/
theorem execute_REMUW_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REMW rs2 rs1 rd true).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_remw_value dividend divisor true)) := by
  rw [execute_REMUW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_remw_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Any successful REMUW run writes Sail's unsigned 32-bit remainder. -/
theorem remuwProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (remuwProgram rs2 rs1 rd q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor true) := by
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let rem := zd - q * zv
  have h_program_succeeds : Program.Run (remuwProgramPhases rs2 rs1 rd q) js js' := by
    rw [← remuwProgram_eq_phases]
    exact hok
  unfold remuwProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, hp4⟩ :=
    Program.Run.append_inv h_program_succeeds

  obtain ⟨hguard1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remuw.phase_setup_run_sound rs1 rs2 q js js₁ dividend divisor
      hrs1 hrs2 hp1

  obtain ⟨hguard2, h2_v0, h2_v1, h2_v3, h2_sail⟩ :=
    Remuw.phase_quotient_product_run_sound js₁ js₂ q zd zv
      h1_v0 h1_v1 h1_v2 hp2

  obtain ⟨hguard3, h3_v3, h3_sail⟩ :=
    Remuw.phase_remainder_bound_run_sound js₂ js₃ q zd zv
      h2_v0 h2_v1 h2_v3 hp3

  have h3_sail_orig : js₃.sail = js.sail :=
    h3_sail.trans (h2_sail.trans h1_sail)
  have hrem :
      sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0) =
        sail_remw_value dividend divisor true := by
    unfold rem
    exact signExtend_remainder_eq_sail_remw_of_guards_uw dividend divisor q
      hguard1 hguard2 hguard3
  have h3_v3_rem : js₃.vregs Remuw.tempVReg = rem := by
    unfold rem
    exact h3_v3
  have hwrite :=
    Remuw.phase_writeback_run_sound rd js₃ js' js.sail
      rem h3_v3_rem h3_sail_orig hp4
  rw [hrem] at hwrite
  exact hwrite

end JoltISA

/-- `REMUW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem remuwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.remuwProgram rs2 rs1 rd quotient)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.remuwProgram rs2 rs1 rd quotient) := by
    unfold JoltISA.remuwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      JoltISA.VRegWritesNoProtectedVReg,
      Remuw.rs1VReg, Remuw.rs2VReg, Remuw.vTmpVReg, Remuw.tempVReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `REMUW` with honest advice. -/
def remuwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = sail_divuw_advice h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.remuwProgram rs2 rs1 rd quotient)).run js) =
    (execute_REMW rs2 rs1 rd true).run js.sail

def remuwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.remuwProgram rs2 rs1 rd quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_remw_value h.rs1_val h.rs2_val true)

def remuwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remuwProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  remuwProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem remuwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remuwProgramEqSailStatement rs2 rs1 rd quotient js h := by
  constructor
  · intro hquotient
    subst quotient
    let dividend := h.rs1_val
    let divisor := h.rs2_val
    have hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail := h.rs1_read
    have hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail := h.rs2_read
    have h_project_initial : System.systemProject js = js.sail := by
      simpa [project] using
        Projection.systemProject_eq_project_of_compatible js h.linkedCSRs
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      unfold JoltISA.remuwProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_REMUW_factored rs2 rs1 (regidx.Regidx 0) true]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.remuwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      remuwProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_divuw_advice dividend divisor) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_REMUW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_remw_value dividend divisor true) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.remuwProgram_sound rs2 rs1 rd quotient js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
