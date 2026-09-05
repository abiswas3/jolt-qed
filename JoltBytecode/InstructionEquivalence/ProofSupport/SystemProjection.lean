import JoltBytecode.Bundles
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.SystemProjection
import JoltBytecode.InstructionEquivalence.ProofSupport.ProtectedVRegWrites
/-!
# System-Projection proof helpers

System projection is a pain the arse. 
It only exists because control status registers are duplicated across
Sails hashmap, and the Jolts virtual reigster file. 
This file contains helper lemmas, that allow us to reduce system_project
to just vanilla project for a large number of instructions.
-/


open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- liftSail changes only js.sail; on both success and error, 
it leaves js.vregs unchanged. It must as its running 
RISC-V computation in a Jolt CPU, and RISC-V has no concept of 
virtual registers.-/
theorem liftSail_preserves_vregs (m : SailM α) (js : SailJoltState) :
    match (liftSail m).run js with
    | .ok _ js' => js'.vregs = js.vregs
    | .error _ js' => js'.vregs = js.vregs := by
  unfold liftSail
  cases h : m js.sail <;> simp only [EStateM.run, h]

/-- Writing to a register that is not protected does not change 
protected registers. 
It's seemingly obvious, but we just have to expand all the cases out once.
-/
theorem writeDst_preserves_protected
    (dst : Dst) (value : BitVec 64) (js : SailJoltState)
    (h : dst.DoesNotWriteProtectedVRegs) :
    match (writeDst dst value).run js with
    | .ok _ js' =>
        ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr
    | .error _ js' =>
        ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  cases dst with
  | xreg rd =>
      have hvregs := liftSail_preserves_vregs (wX_bits rd value) js
      cases hrun : (liftSail (wX_bits rd value)).run js with
      | ok result js' =>
          rw [hrun] at hvregs
          simp only [writeDst, hrun]
          intro vr _
          exact congrFun hvregs vr
      | error error js' =>
          rw [hrun] at hvregs
          simp only [writeDst, hrun]
          intro vr _
          exact congrFun hvregs vr
  | vreg written =>
      unfold Dst.DoesNotWriteProtectedVRegs Dst.WritesProtectedVReg at h
      unfold writeDst writeVReg
      by_cases hwritable : written.toNat < 32
      · simp only [hwritable, ↓reduceIte, EStateM.run, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw]
        intro vr _
        trivial
      · simp only [hwritable, ↓reduceIte, EStateM.run, modify, modifyGet,
          MonadStateOf.modifyGet, EStateM.modifyGet]
        intro vr hprotected
        by_cases heq : vr = written
        · subst vr
          exact False.elim (h hprotected)
        · simp only [heq, ↓reduceIte]

/-- If instr is classified as not writing protected virtual registers, 
then after executing it, every protected virtual register 
has exactly its original value—whether execution succeeds or errors. -/
theorem execInstr_preserves_protected
    (instr : Instr) (js : SailJoltState)
    (h : instr.DoesNotWriteProtectedVRegs) :
    match (execInstr instr).run js with
    | .ok _ js' =>
        ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr
    | .error _ js' =>
        ∀ vr, IsProtectedJoltRegister vr → js'.vregs vr = js.vregs vr := by
  sorry

end JoltISA

namespace System

/-- Re-inserting a dependent-map value that is already present leaves the map
unchanged. -/
theorem extDHashMap_insert_eq_self_of_get? {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] {β : α → Type} (m : Std.ExtDHashMap α β) (k : α)
    (v : β k) (h : m.get? k = some v) :
    m.insert k v = m := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  rw [Std.ExtDHashMap.get?_insert]
  split
  · rename_i hbeq
    have heq : k = a := LawfulBEq.eq_of_beq hbeq
    cases heq
    rw [h]
    rw [cast_eq]
  · rfl

/-- If the linked CSR virtual registers agree with the generated Sail CSR
registers, materializing those virtual registers is the same state as the plain
projection. This is the global linked-register invariant made explicit. -/
theorem systemProject_eq_project_of_compatible
    (js : SailJoltState)
    (h : LinkedCSRs js) :
    systemProject js = project js := by
  have hMstatus := h.1
  have hMtvec := h.2.1
  have hMscratch := h.2.2.1
  have hMepc := h.2.2.2.1
  have hMcause := h.2.2.2.2.1
  have hMtval := h.2.2.2.2.2
  unfold systemProject project
  simp only
  congr
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtvec
    (js.vregs JoltISA.trapHandlerVReg) hMtvec.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mscratch
    (js.vregs JoltISA.mscratchVReg) hMscratch.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mepc
    (js.vregs JoltISA.mepcVReg) hMepc.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mcause
    (js.vregs JoltISA.mcauseVReg) hMcause.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mtval
    (js.vregs JoltISA.mtvalVReg) hMtval.value_eq]
  rw [extDHashMap_insert_eq_self_of_get? js.sail.regs Register.mstatus
    (js.vregs JoltISA.mstatusVReg) hMstatus.value_eq]

/--If initial jolt state has control status registers in virtual reg file and 
sail reg file set as equal, and the jolt instruction does not write to 
protected regs, then the two reg files still remain in sync-/
theorem execInstr_preservesLinkedCSRs
    (instr : JoltISA.Instr) (js : SailJoltState)
    (hlinked : LinkedCSRs js)
    (h : instr.DoesNotWriteProtectedVRegs) :
    match (JoltISA.execInstr instr).run js with
    | .ok _ js' => LinkedCSRs js'
    | .error _ js' => LinkedCSRs js' := by
  sorry

/-- If Jolt instruction does not write to protected registers, 
then it is safe to replace systemProjectResult with just 
projectResult
-/
theorem systemProjectResult_execInstr_eq_projectResult
    (instr : JoltISA.Instr) (js : SailJoltState)
    (hlinked : LinkedCSRs js)
    (h : instr.DoesNotWriteProtectedVRegs) :
    systemProjectResult ((JoltISA.execInstr instr).run js) =
      projectResult ((JoltISA.execInstr instr).run js) := by
  have hpreserved := execInstr_preservesLinkedCSRs instr js hlinked h
  cases hrun : (JoltISA.execInstr instr).run js with
  | ok result js' =>
      have hlinked' : LinkedCSRs js' := by
        simpa only [hrun] using hpreserved
      simp only [systemProjectResult, projectResult]
      rw [systemProject_eq_project_of_compatible js' hlinked']
  | error error js' =>
      have hlinked' : LinkedCSRs js' := by
        simpa only [hrun] using hpreserved
      simp only [systemProjectResult, projectResult]
      rw [systemProject_eq_project_of_compatible js' hlinked']

/-- If a Jolt Program does not write to protected registers, 
then it is safe to replace systemProjectResult with just 
projectResult
-/
theorem systemProjectResult_execProgram_eq_projectResult
    (program : JoltISA.Program) (js : SailJoltState)
    (hlinked : LinkedCSRs js)
    (h : program.DoesNotWriteProtectedVRegs) :
    systemProjectResult ((JoltISA.execProgram program).run js) =
      projectResult ((JoltISA.execProgram program).run js) := by
  induction program generalizing js with
  | done result =>
      simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.run,
        systemProjectResult, projectResult]
      rw [systemProject_eq_project_of_compatible js hlinked]
  | instr instr rest ih =>
      rw [JoltISA.Program.instr_doesNotWriteProtectedVRegs_iff] at h
      have hhead := execInstr_preservesLinkedCSRs instr js hlinked h.1
      simp only [JoltISA.execProgram, bind, EStateM.bind, EStateM.run]
      cases hinstr : JoltISA.execInstr instr js with
      | error error js' =>
          have hlinked' : LinkedCSRs js' := by
            simpa only [EStateM.run, hinstr] using hhead
          simp only [systemProjectResult, projectResult]
          rw [systemProject_eq_project_of_compatible js' hlinked']
      | ok result js' =>
          have hlinked' : LinkedCSRs js' := by
            simpa only [EStateM.run, hinstr] using hhead
          cases result <;>
            simp only [pure, EStateM.pure, systemProjectResult, projectResult]
          · exact ih js' hlinked' h.2
          all_goals
            rw [systemProject_eq_project_of_compatible js' hlinked']

end System

end
