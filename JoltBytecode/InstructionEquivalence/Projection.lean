import JoltBytecode.JoltISA.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.System.Bundles

/-!
# Projection proof facts

These are proof-facing facts about `JoltISA.project2`.  They intentionally live
outside `JoltISA` because they mention public proof assumptions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Projection

/-- Public invariant that the persistent CSR virtual registers currently agree
with the generated Sail CSR register map. -/
abbrev LinkedCSRs (js : SailJoltState) : Prop :=
  Assumptions.MstatusVRegMatchesSail js ∧
  Assumptions.MtvecVRegMatchesSail js ∧
  Assumptions.MscratchVRegMatchesSail js ∧
  Assumptions.MepcVRegMatchesSail js ∧
  Assumptions.McauseVRegMatchesSail js ∧
  Assumptions.MtvalVRegMatchesSail js

/-- The persistent CSR virtual registers materialized by `project2` are
unchanged between two Jolt states. -/
def ProjectedVRegsPreserved (before after : SailJoltState) : Prop :=
  after.vregs JoltISA.trapHandlerVReg = before.vregs JoltISA.trapHandlerVReg ∧
  after.vregs JoltISA.mscratchVReg = before.vregs JoltISA.mscratchVReg ∧
  after.vregs JoltISA.mepcVReg = before.vregs JoltISA.mepcVReg ∧
  after.vregs JoltISA.mcauseVReg = before.vregs JoltISA.mcauseVReg ∧
  after.vregs JoltISA.mtvalVReg = before.vregs JoltISA.mtvalVReg ∧
  after.vregs JoltISA.mstatusVReg = before.vregs JoltISA.mstatusVReg

/-- Under the linked-CSR invariant, `project2` agrees with the old plain
projection on the initial state. -/
theorem project2_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    JoltISA.project2 js = project js := by
  change System.systemProject js = project js
  exact System.systemProject_eq_project_of_compatible js h

/-- Projecting after an architectural x-register write is the same as writing
that x-register after projecting. -/
theorem project2_stateAfterWrite
    (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    JoltISA.project2 { js with sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (JoltISA.project2 js) rd value := by
  change System.systemProject { js with sail := stateAfterWrite js.sail rd value } =
    stateAfterWrite (System.systemProject js) rd value
  exact System.systemProject_stateAfterWrite js rd value

/-- If an instruction updates only the embedded Sail state and preserves the
CSR virtual registers projected by `project2`, then projection commutes with
that architectural x-register write. -/
theorem project2_stateAfterWrite_of_projected_vregs_preserved
    (before after : SailJoltState) (rd : regidx) (value : BitVec 64)
    (hsail : after.sail = stateAfterWrite before.sail rd value)
    (hprojected : ProjectedVRegsPreserved before after) :
    JoltISA.project2 after = stateAfterWrite (JoltISA.project2 before) rd value := by
  have hsame :
      JoltISA.project2 after =
        JoltISA.project2 { before with sail := stateAfterWrite before.sail rd value } := by
    rcases hprojected with
      ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus⟩
    unfold JoltISA.project2
    simp only [hsail, hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus]
  rw [hsame]
  exact project2_stateAfterWrite before rd value

/-- Generic projected-vreg preservation theorem for any successful program run
whose instructions avoid protected Jolt registers.  The old classifier is
stronger than needed for `project2`, but it gives a reusable bridge while the
projection contract is being rolled out. -/
theorem execProgram_preserves_projected_vregs_of_no_protected_writes
    {program : JoltISA.Program}
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hsafe : JoltISA.ProgramWritesNoProtectedVReg program)
    (hrun : (JoltISA.execProgram program).run js = .ok result js') :
    ProjectedVRegsPreserved js js' := by
  have hprotected :=
    JoltISA.execProgram_preserves_protected
      (js := js) (js' := js') (result := result) hsafe hrun
  exact ⟨
    hprotected JoltISA.trapHandlerVReg rfl,
    hprotected JoltISA.mscratchVReg rfl,
    hprotected JoltISA.mepcVReg rfl,
    hprotected JoltISA.mcauseVReg rfl,
    hprotected JoltISA.mtvalVReg rfl,
    hprotected JoltISA.mstatusVReg rfl⟩

end Projection

end
