import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Projection
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW

Jolt program sequence:
1. `ADD rd, rs1, rs2` — 64-bit add, writes `v1 + v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Sail's ADDW extracts lower 32 bits of each operand, adds them at 32
bits, and sign-extends to 64. The local value lemma says truncation
distributes over addition, so both sides produce the same result.
-/

abbrev addw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)

abbrev addw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + v2) 31 0)

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.ADDW` reads `rs1`, reads
`rs2`, writes `addw_sail_operation v1 v2` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_ADDW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (addw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, addw_sail_operation]

/-- `(a + b)[31:0] = a[31:0] + b[31:0]`. -/
private theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail ADDW value
`h(v1, v2)`. -/
private theorem addw_value_eq_sail (v1 v2 : BitVec 64) :
    addw_jolt_val v1 v2 = addw_sail_operation v1 v2 := by
  simp only [addw_jolt_val, addw_sail_operation]
  rw [extractLsb_add]

/-- Public assumptions for `ADDW` under the `project2` contract.

The source-read fields drive the ADDW execution proof.  The linked-CSR fields
state that the persistent CSR virtual registers already agree with the Sail CSR
registers, so projecting Jolt state with `project2` starts from the same Sail
state as the Sail instruction. -/
structure AddwProgramEqSailAssumptions
    (rs2 rs1 : regidx) (js : SailJoltState) : Type where
  source_reads : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js
  linked_csrs : Projection.LinkedCSRs js

/-- Program-level concrete theorem for `ADDW`.

The new Jolt-ISA program states the Rust-style expansion directly:
architectural `ADD`, followed by the virtual sign-extend-word instruction.
The proof exposes the two real writes and collapses them to the final
sign-extended architectural write. -/
theorem addwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (addw_sail_operation v1 v2) ∧
      js'.vregs = js.vregs := by

    -- Instruction 1: `ADD rd, rs1, rs2` writes the 64-bit sum to `rd`.
    let sum := v1 + v2
    obtain ⟨s_afterAdd, h_write_sum⟩ := wX_shape rd sum js.sail
    let js_afterAdd : SailJoltState := { sail := s_afterAdd, vregs := js.vregs }
    have h_add_writes_sum :
        js_afterAdd.sail = stateAfterWrite js.sail rd sum :=
      wX_bits_eq_stateAfterWrite rd sum js.sail s_afterAdd h_write_sum
    have h_add_succeeds :
        (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
          .ok RETIRE_SUCCESS js_afterAdd :=
      JoltISA.add_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 s_afterAdd
        h_read_rs1 h_read_rs2 h_write_sum

    -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the ADDW result.
    let jolt_val := addw_jolt_val v1 v2
    have h_source_reads_sum : rX_bits rd js_afterAdd.sail = .ok sum js_afterAdd.sail := by
      rw [h_add_writes_sum]
      exact rX_after_stateAfterWrite rd sum js.sail hrd
    obtain ⟨s_afterSignExtend, h_write_jolt⟩ := wX_shape rd jolt_val js_afterAdd.sail
    let js_afterSignExtend : SailJoltState :=
      { sail := s_afterSignExtend, vregs := js.vregs }
    have h_sign_extend_succeeds :
        (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run
            js_afterAdd =
          .ok RETIRE_SUCCESS js_afterSignExtend :=
      JoltISA.virtual_sign_extend_word_run_xreg_xreg rd rd js_afterAdd sum
        s_afterSignExtend h_source_reads_sum h_write_jolt

    -- Full program succeeds by stepping through the two instruction runs.
    have h_program_succeeds :
        (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js_afterSignExtend := by
      unfold JoltISA.addwProgram
      rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAdd h_add_succeeds]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAdd js_afterSignExtend
        h_sign_extend_succeeds]
      rfl

    refine ⟨js_afterSignExtend, h_program_succeeds, ?_, rfl⟩

    -- The instruction trace leaves `rd` containing the Jolt ADDW value.
    have h_final_jolt_value :
        js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
      have h_sail_after_sign_extend :
          js_afterSignExtend.sail = stateAfterWrite js_afterAdd.sail rd jolt_val :=
        wX_bits_eq_stateAfterWrite rd jolt_val js_afterAdd.sail
          s_afterSignExtend h_write_jolt
      rw [h_sail_after_sign_extend, h_add_writes_sum]
      exact stateAfterWrite_stateAfterWrite rd sum jolt_val js.sail

    -- No more execution reasoning remains.
    -- The only real content left is the pure value equality:
    -- Jolt's two-instruction value is Sail's ADDW value.
    have h_addw_value :
        jolt_val = addw_sail_operation v1 v2 := by
      simp only [jolt_val]
      -- NOTE: The core math theorem.
      exact addw_value_eq_sail v1 v2

    -- After the value theorem, the final state claim is mechanical.
    rw [← h_addw_value]
    exact h_final_jolt_value

/-- Rust's ADDW `rd = x0` replacement `ADDI x0, x0, 0` retires successfully
and leaves the projected Sail state unchanged. -/
private theorem addw_rd_zero_noop_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (js : SailJoltState) :
    (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 (regidx.Regidx 0))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold JoltISA.addwProgram
  rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
  exact JoltISA.pureWritebackRdZeroProgram_run js

/-- `ADDW` never writes the persistent CSR virtual registers materialized by
`project2`. -/
theorem addwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.addwProgram rs2 rs1 rd) := by
    unfold JoltISA.addwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `ADDW`. -/
def addwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : AddwProgramEqSailAssumptions rs2 rs1 js) : Prop :=
  JoltISA.projectResult2
      ((JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail

theorem addwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : AddwProgramEqSailAssumptions rs2 rs1 js) :
    addwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold addwProgramEqSailStatement
  let v1 := h.source_reads.rs1_val
  let v2 := h.source_reads.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail :=
    h.source_reads.rs1_read
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail :=
    h.source_reads.rs2_read
  have h_project_initial : JoltISA.project2 js = js.sail := by
    simpa [project] using
      Projection.project2_eq_project_of_compatible js h.linked_csrs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    rw [addw_rd_zero_noop_concrete rs2 rs1 js]
    simp only [JoltISA.projectResult2]
    rw [h_project_initial]
    rw [execute_RTYPEW_ADDW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail,
      _h_final_vregs⟩ :=
    addwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSignExtend :=
    addwProgram_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [JoltISA.projectResult2]

  rw [execute_RTYPEW_ADDW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (addw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.project2_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSignExtend rd (addw_sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (addw_sail_operation v1 v2)
    js.sail s' h_write).symm

end
