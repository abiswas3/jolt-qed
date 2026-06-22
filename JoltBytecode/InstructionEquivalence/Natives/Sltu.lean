import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Semantics.Instructions.SLTU

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Factoring: `execute_RTYPE rs2 rs1 rd rop.SLTU` reads `rs1`, reads `rs2`,
writes the unsigned less-than flag to `rd`, and returns `RETIRE_SUCCESS`. -/
theorem execute_RTYPE_SLTU_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLTU = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (jolt_sltu_value v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE, jolt_sltu_value]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Native `SLTU` never writes the persistent CSR virtual registers materialized
by `systemProject`. -/
theorem sltuInstr_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun :
      (JoltISA.execInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.InstrWritesNoProtectedVReg
        (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2)) := by
    simp only [JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  have hprotected :=
    JoltISA.execInstr_preserves_protected
      (instr := .SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

/-- Main native `SLTU` equivalence statement. -/
def sltuInstrEqSailStatement
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js) =
    ((execute_RTYPE rs2 rs1 rd rop.SLTU).run js.sail)

private theorem sltuInstr_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    ∃ js',
      (JoltISA.execInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (jolt_sltu_value v1 v2) ∧
      js'.vregs = js.vregs := by
  obtain ⟨s', hwrite⟩ := wX_shape rd (jolt_sltu_value v1 v2) js.sail
  let js' : SailJoltState := { sail := s', vregs := js.vregs }
  have h_sail : js'.sail = stateAfterWrite js.sail rd (jolt_sltu_value v1 v2) :=
    wX_bits_eq_stateAfterWrite rd (jolt_sltu_value v1 v2) js.sail s' hwrite
  have h_run :
      (JoltISA.execInstr (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.sltu_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 s'
      h_read_rs1 h_read_rs2 hwrite
  exact ⟨js', h_run, h_sail, rfl⟩

theorem sltuInstr_eq_sail
    (rs2 rs1 rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    sltuInstrEqSailStatement rs2 rs1 rd js h := by
  unfold sltuInstrEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs

  obtain ⟨js_afterSltu, h_run, h_final_sail, _h_final_vregs⟩ :=
    sltuInstr_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSltu :=
    sltuInstr_preserves_projected_vregs rs2 rs1 rd h_run

  rw [h_run]
  simp only [System.systemProjectResult]

  rw [execute_RTYPE_SLTU_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (jolt_sltu_value v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSltu rd (jolt_sltu_value v1 v2) h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (jolt_sltu_value v1 v2) js.sail s'
    h_write).symm

end Natives

end
