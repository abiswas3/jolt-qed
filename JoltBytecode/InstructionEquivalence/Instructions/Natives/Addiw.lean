import JoltBytecode.JoltISA.Core
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `ADDIW` equivalence statement. -/
def addiwInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.ADDIW (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_ADDIW imm rs1 rd).run js.sail)

private abbrev op (rs1_val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  jolt_addiw_value rs1_val imm

/-- TODO: Docs -/
theorem addiwInstr_doesNotWriteProtectedVRegs
    (imm : BitVec 12)
    (rs1 rd : regidx) :
    (JoltISA.Instr.ADDIW (.xreg rd) (.xreg rs1) imm).DoesNotWriteProtectedVRegs := by
  exact JoltISA.Dst.xreg_doesNotWriteProtectedVRegs rd

/-- Native `ADDIW` agrees with Sail `execute_ADDIW`. -/
theorem addiwInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    addiwInstrEqSailStatement imm rs1 rd js h := by
  unfold addiwInstrEqSailStatement
  -- SystemProject = Project as this instruction does not 
  -- write to proteced registers.
  rw [System.systemProjectResult_execInstr_eq_projectResult
    (.ADDIW (.xreg rd) (.xreg rs1) imm) js h.linkedCSRs
    (addiwInstr_doesNotWriteProtectedVRegs imm rs1 rd)]
  -- Sail side
  simp only [execute_ADDIW, EStateM.run, bind, EStateM.bind]
  simp only [h.rs1_read]
  simp only [pure, EStateM.pure]
  rw [sail_addiw_value_eq_jolt_addiw_value]
  obtain ⟨s', h_write⟩ := wX_shape rd (op h.rs1_val imm) js.sail
  simp only [h_write]
  -- Jolt side
  simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h.rs1_read, h_write]
  simp only [pure, EStateM.pure, projectResult, project]

end Natives

end
