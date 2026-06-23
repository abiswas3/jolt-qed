import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ADDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

Jolt program sequence:
1. `ADDI rd, rs1, imm` — writes `v + sign_extend imm` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`
-/

theorem execute_ITYPE_ADDI_factored (imm : BitVec 12) (rs1 rd : regidx) :
  execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v ← rX_bits rs1
      wX_bits rd (v + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp [execute_ITYPE, bind_pure_comp]

abbrev addiw_sail_operation (imm : BitVec 12) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)

abbrev addiw_jolt_val (imm : BitVec 12) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)

private theorem addiw_value_eq_sail (imm : BitVec 12) (v : BitVec 64) :
    addiw_jolt_val imm v = addiw_sail_operation imm v := by
  rfl

theorem execute_ADDIW_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = (do
      let v ← rX_bits rs1
      wX_bits rd (addiw_sail_operation imm v)
      pure RETIRE_SUCCESS) := by
  simp [execute_ADDIW, bind_pure_comp, pure_bind, addiw_sail_operation]

/-- Program-level concrete theorem for `ADDIW`.

The program is architectural `ADDI`, then `VirtualSignExtendWord rd, rd`.  As with the R-type
W proofs, the two architectural writes collapse to the final sign-extended
write. -/
theorem addiwProgram_concrete (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (addiw_sail_operation imm v) := by

  -- Instruction 1: `ADDI rd, rs1, imm` writes the 64-bit sum to `rd`.
  let sum := v + sign_extend (m := 64) imm
  obtain ⟨js_afterAddi, h_addi_reads_rs1, h_addi_writes_sum, h_addi_succeeds⟩ :=
    JoltISA.exists_state_after_addi_run_xreg_xreg rd rs1 imm js v h_read_rs1

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the ADDIW result.
  let jolt_val := addiw_jolt_val imm v
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val,
      h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterAddi js.sail sum h_addi_writes_sum

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.addiwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAddi h_addi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAddi js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt ADDIW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's ADDIW value.
  have h_addiw_value :
      jolt_val = addiw_sail_operation imm v := by
    -- NOTE: The core math theorem.
    exact addiw_value_eq_sail imm v

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_addiw_value]
  exact h_final_jolt_value

/-- `ADDIW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem addiwProgram_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.addiwProgram imm rs1 rd) := by
    unfold JoltISA.addiwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      true_and]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `ADDIW`. -/
def addiwProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js) =
    (execute_ADDIW imm rs1 rd).run js.sail

/-- Main program-level equivalence for `ADDIW`. -/
theorem addiwProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiwProgramEqSailStatement imm rs1 rd js h := by
  unfold addiwProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.addiwProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_ADDIW_factored imm rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    addiwProgram_concrete imm rs1 rd js v h_read_rs1 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSignExtend :=
    addiwProgram_preserves_projected_vregs imm rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_ADDIW_factored imm rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (addiw_sail_operation imm v) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSignExtend rd (addiw_sail_operation imm v)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (addiw_sail_operation imm v)
    js.sail s' h_write).symm

end
