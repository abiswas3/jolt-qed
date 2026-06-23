import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Factoring: `execute_ITYPE imm rs1 rd iop.ADDI` reads `rs1`, writes the
sign-extended immediate sum to `rd`, and returns `RETIRE_SUCCESS`. -/
theorem execute_ITYPE_ADDI_factored
    (imm : BitVec 12)
    (rs1 rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v1 ← rX_bits rs1
      wX_bits rd (v1 + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp only [execute_ITYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- RHS as final state: running native Sail `ADDI` reads `rs1 = v1`, then leaves
the Sail state as `s` with `rd` overwritten by `v1 + sign_extend imm`. -/
theorem execute_ITYPE_ADDI_run
    (imm : BitVec 12) (rs1 rd : regidx) (s : SailState) (v1 : BitVec 64)
    (h_read : rX_bits rs1 s = .ok v1 s) :
    (execute_ITYPE imm rs1 rd iop.ADDI).run s =
      .ok RETIRE_SUCCESS (stateAfterWrite s rd (v1 + sign_extend (m := 64) imm)) := by
  rw [execute_ITYPE_ADDI_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read]
  obtain ⟨s', h_write⟩ := wX_shape rd (v1 + sign_extend (m := 64) imm) s
  rw [h_write]
  rw [wX_bits_eq_stateAfterWrite rd (v1 + sign_extend (m := 64) imm) s s' h_write]

/-- Native `ADDI` never writes the persistent CSR virtual registers materialized
by `systemProject`, so projection commutes with the architectural write. -/
theorem addiInstr_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.InstrWritesNoProtectedVReg
        (.ADDI (.xreg rd) (.xreg rs1) imm) := by
    simp only [JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  have hprotected :=
    JoltISA.execInstr_preserves_protected
      (instr := .ADDI (.xreg rd) (.xreg rs1) imm)
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

/-- Main native `ADDI` equivalence statement. -/
def addiInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ITYPE imm rs1 rd iop.ADDI).run js.sail)


theorem addiInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiInstrEqSailStatement imm rs1 rd js h := by
  unfold addiInstrEqSailStatement 
  rw [execute_ITYPE_ADDI_run imm rs1 rd js.sail h.rs1_val h.rs1_read]
  -- Decompose the LHS Jolt run into its concrete post-state `js_afterAddi`.
  obtain ⟨js_afterAddi, _h_reads, h_final_sail, h_run⟩ :=
    JoltISA.exists_state_after_addi_run_xreg_xreg rd rs1 imm js h.rs1_val h.rs1_read
  rw [h_run]
  simp only [System.systemProjectResult]
  -- LHS is now `.ok RETIRE_SUCCESS (System.systemProject js_afterAddi)`.
  simp only [EStateM.Result.ok.injEq, true_and]
  -- Goal: System.systemProject js_afterAddi
  --         = stateAfterWrite js.sail rd (h.rs1_val + sign_extend imm)
  -- Rewrite the bare `js.sail` into `System.systemProject js`.
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  rw [← h_project_initial]
  -- Goal: System.systemProject js_afterAddi
  --         = stateAfterWrite (System.systemProject js) rd (h.rs1_val + sign_extend imm)
  -- ADDI preserves the projected CSR vregs, so projection commutes with the write.
  have h_projected_vregs : Projection.ProjectedVRegsPreserved js js_afterAddi :=
    addiInstr_preserves_projected_vregs imm rs1 rd h_run
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterAddi rd (h.rs1_val + sign_extend (m := 64) imm)
    h_final_sail h_projected_vregs]



end Natives

end
