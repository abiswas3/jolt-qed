import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LUI

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Factoring: `execute_UTYPE imm rd uop.LUI` writes the normalized immediate
to `rd` and returns `RETIRE_SUCCESS`. -/
theorem execute_UTYPE_LUI_factored
    (imm : BitVec 20)
    (rd : regidx) :
    execute_UTYPE imm rd uop.LUI = (do
      wX_bits rd (JoltISA.luiValue imm)
      pure RETIRE_SUCCESS) := by
  simp only [execute_UTYPE, JoltISA.luiValue]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [pure_bind]

/-- Native `LUI` never writes the persistent CSR virtual registers materialized
by `systemProject`. -/
theorem luiInstr_preserves_projected_vregs
    (imm : BitVec 20)
    (rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execLUI imm rd).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.InstrWritesNoProtectedVReg
        (.LUI (.xreg rd) (JoltISA.luiValue imm)) := by
    simp only [JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  have hprotected :=
    JoltISA.execInstr_preserves_protected
      (instr := .LUI (.xreg rd) (JoltISA.luiValue imm))
      (js := js) (js' := js') (result := result) hsafe
      (by simpa [JoltISA.execLUI] using hrun)
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

/-- Main native `LUI` equivalence statement. -/
def luiInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execLUI imm rd).run js) =
    ((execute_UTYPE imm rd uop.LUI).run js.sail)

private theorem luiInstr_concrete
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState) :
    ∃ js',
      (JoltISA.execLUI imm rd).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (JoltISA.luiValue imm) ∧
      js'.vregs = js.vregs := by
  obtain ⟨s', hwrite⟩ := wX_shape rd (JoltISA.luiValue imm) js.sail
  let js' : SailJoltState := { sail := s', vregs := js.vregs }
  have h_sail : js'.sail =
      stateAfterWrite js.sail rd (JoltISA.luiValue imm) :=
    wX_bits_eq_stateAfterWrite rd (JoltISA.luiValue imm) js.sail s' hwrite
  have h_run :
      (JoltISA.execLUI imm rd).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.execLUI JoltISA.execInstr JoltISA.writeDst liftSail
    simp only [hwrite, js', bind, EStateM.bind, pure, EStateM.pure,
      EStateM.run]
  exact ⟨js', h_run, h_sail, rfl⟩

/-- Native `LUI` writes the normalized immediate in both Jolt and Sail. -/
theorem luiInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    luiInstrEqSailStatement imm rd js h := by
  unfold luiInstrEqSailStatement
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs

  obtain ⟨js_afterLui, h_run, h_final_sail, _h_final_vregs⟩ :=
    luiInstr_concrete imm rd js
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterLui :=
    luiInstr_preserves_projected_vregs imm rd h_run

  rw [h_run]
  simp only [System.systemProjectResult]

  rw [execute_UTYPE_LUI_factored imm rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]

  obtain ⟨s', h_write⟩ := wX_shape rd (JoltISA.luiValue imm) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterLui rd (JoltISA.luiValue imm) h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (JoltISA.luiValue imm)
    js.sail s' h_write).symm

end Natives

end
