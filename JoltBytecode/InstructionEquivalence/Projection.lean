import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

/-!
# Projection proof facts

These are proof-facing facts about `System.systemProject`.
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

/-- The persistent CSR virtual registers materialized by `systemProject` are
unchanged between two Jolt states. -/
def ProjectedVRegsPreserved (before after : SailJoltState) : Prop :=
  after.vregs JoltISA.trapHandlerVReg = before.vregs JoltISA.trapHandlerVReg ∧
  after.vregs JoltISA.mscratchVReg = before.vregs JoltISA.mscratchVReg ∧
  after.vregs JoltISA.mepcVReg = before.vregs JoltISA.mepcVReg ∧
  after.vregs JoltISA.mcauseVReg = before.vregs JoltISA.mcauseVReg ∧
  after.vregs JoltISA.mtvalVReg = before.vregs JoltISA.mtvalVReg ∧
  after.vregs JoltISA.mstatusVReg = before.vregs JoltISA.mstatusVReg

/-- Under the linked-CSR invariant, `systemProject` agrees with the old plain
projection on the initial state. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    System.systemProject js = project js :=
  System.systemProject_eq_project_of_compatible js h

/-- Under the linked-CSR invariant, `systemProject` agrees with the embedded
generated Sail state. This is the instruction-facing form; callers should not
need to mention the legacy plain projection. -/
theorem systemProject_eq_sail_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    System.systemProject js = js.sail :=
  System.systemProject_eq_project_of_compatible js h

/-- Projecting after an architectural x-register write is the same as writing
that x-register after projecting. -/
theorem systemProject_stateAfterWrite
    (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    System.systemProject { js with sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (System.systemProject js) rd value :=
  System.systemProject_stateAfterWrite js rd value

/-- If an instruction updates only the embedded Sail state and preserves the
CSR virtual registers projected by `systemProject`, then projection commutes with
that architectural x-register write. -/
theorem systemProject_stateAfterWrite_of_projected_vregs_preserved
    (before after : SailJoltState) (rd : regidx) (value : BitVec 64)
    (hsail : after.sail = stateAfterWrite before.sail rd value)
    (hprojected : ProjectedVRegsPreserved before after) :
    System.systemProject after = stateAfterWrite (System.systemProject before) rd value := by
  have hsame :
      System.systemProject after =
        System.systemProject { before with sail := stateAfterWrite before.sail rd value } := by
    rcases hprojected with
      ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus⟩
    unfold System.systemProject
    simp only [hsail, hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus]
  rw [hsame]
  exact systemProject_stateAfterWrite before rd value

/-- If a transition preserves the projected CSR virtual registers and leaves
the generated Sail register map unchanged, then linked CSRs remain linked after
the transition. This is the store-family projection bridge: stores update
memory, not registers. -/
theorem systemProject_eq_project_of_projected_vregs_preserved_of_sail_regs_eq
    (before after : SailJoltState)
    (hregs : after.sail.regs = before.sail.regs)
    (hprojected : ProjectedVRegsPreserved before after)
    (hlinked : LinkedCSRs before) :
    System.systemProject after = project after := by
  rcases hprojected with
    ⟨hmtvec, hmscratch, hmepc, hmcause, hmtval, hmstatus⟩
  rcases hlinked with
    ⟨hmstatusLinked, hmtvecLinked, hmscratchLinked, hmepcLinked,
      hmcauseLinked, hmtvalLinked⟩
  have hlinked_after : LinkedCSRs after := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨by rw [hregs, hmstatus, hmstatusLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmtvec, hmtvecLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmscratch, hmscratchLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmepc, hmepcLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmcause, hmcauseLinked.value_eq]⟩
    · exact ⟨by rw [hregs, hmtval, hmtvalLinked.value_eq]⟩
  exact systemProject_eq_project_of_compatible after hlinked_after

/-- Instruction-facing store-family projection bridge: if the transition
preserves projected CSR virtual registers and leaves the Sail register map
unchanged, `systemProject` agrees with the final embedded Sail state. -/
theorem systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
    (before after : SailJoltState)
    (hregs : after.sail.regs = before.sail.regs)
    (hprojected : ProjectedVRegsPreserved before after)
    (hlinked : LinkedCSRs before) :
    System.systemProject after = after.sail :=
  systemProject_eq_project_of_projected_vregs_preserved_of_sail_regs_eq
    before after hregs hprojected hlinked

/-- Generic projected-vreg preservation theorem for any successful program run
whose instructions avoid protected Jolt registers.  The old classifier is
stronger than needed for `systemProject`, but it gives a reusable bridge. -/
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
