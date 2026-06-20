import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.Sub
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SUBW: Jolt SUB + VirtualSignExtendWord = Sail SUBW

Jolt program sequence:
1. `SUB rd, rs1, rs2` — 64-bit subtract, writes `v1 - v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Identical in shape to `ADDW`; the only differences are the operation
(`rop.SUB` / `ropw.SUBW`) and the bridge (`extractLsb_sub`).
-/

abbrev subw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)

abbrev subw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 - v2) 31 0)

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.SUBW` reads `rs1`, reads
`rs2`, writes `subw_sail_operation v1 v2` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_SUBW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (subw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, subw_sail_operation]

/-- `(a - b)[31:0] = a[31:0] - b[31:0]`. -/
private theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail SUBW value
`h(v1, v2)`. -/
private theorem subw_value_eq_sail (v1 v2 : BitVec 64) :
    subw_jolt_val v1 v2 = subw_sail_operation v1 v2 := by
  simp only [subw_jolt_val, subw_sail_operation]
  rw [extractLsb_sub]

/-- Program-level concrete theorem for `SUBW`.

The program is the same two-step shape as `ADDW`: do the 64-bit architectural
subtraction, then sign-extend the low word of `rd`. -/
theorem subwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (subw_sail_operation v1 v2) := by
    -- Instruction 1: `SUB rd, rs1, rs2` writes the 64-bit difference to `rd`.
    let difference := v1 - v2
    obtain ⟨js_afterSub, h_sub_reads_rs1, h_sub_reads_rs2,
        h_sub_writes_difference, h_sub_succeeds⟩ :=
      JoltISA.exists_state_after_sub_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 h_read_rs1 h_read_rs2

    -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SUBW result.
    let jolt_val := subw_jolt_val v1 v2
    obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
      JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
        rd js_afterSub js.sail difference h_sub_writes_difference

    -- Full program succeeds by stepping through the two instruction runs.
    have h_program_succeeds :
        (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js_afterSignExtend := by
      unfold JoltISA.subwProgram
      rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub h_sub_succeeds]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSub js_afterSignExtend
        h_sign_extend_succeeds]
      rfl

    refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

    -- The instruction trace leaves `rd` containing the Jolt SUBW value.
    have h_final_jolt_value :
        js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
      exact h_sign_extend_writes_jolt_val

    -- No more execution reasoning remains.
    -- The only real content left is the pure value equality:
    -- Jolt's two-instruction value is Sail's SUBW value.
    have h_subw_value :
        jolt_val = subw_sail_operation v1 v2 := by
      simp only [jolt_val]
      -- NOTE: The core math theorem.
      exact subw_value_eq_sail v1 v2

    -- After the value theorem, the final state claim is mechanical.
    rw [← h_subw_value]
    exact h_final_jolt_value

/-- `SUBW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem subwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.subwProgram rs2 rs1 rd) := by
    unfold JoltISA.subwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      true_and]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `SUBW`. -/
def subwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail

/-- Main program-level equivalence for `SUBW`. -/
theorem subwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    subwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold subwProgramEqSailStatement
  obtain ⟨v1, h_read_rs1⟩ := h.rs1_readable.exists_value
  obtain ⟨v2, h_read_rs2⟩ := h.rs2_readable.exists_value
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.subwProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_RTYPEW_SUBW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    subwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSignExtend :=
    subwProgram_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_RTYPEW_SUBW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (subw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSignExtend rd (subw_sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (subw_sail_operation v1 v2)
    js.sail s' h_write).symm

end
