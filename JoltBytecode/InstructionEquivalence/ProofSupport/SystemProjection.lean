import JoltBytecode.Bundles
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.SystemProjection
import JoltBytecode.InstructionEquivalence.ProofSupport.ProtectedVRegWrites

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- TODO: Docs -/
theorem systemProjectResult_execInstr_eq_projectResult
    (instr : JoltISA.Instr) (js : SailJoltState)
    (hlinked : LinkedCSRs js)
    (h : instr.DoesNotWriteProtectedVRegs) :
    systemProjectResult ((JoltISA.execInstr instr).run js) =
      projectResult ((JoltISA.execInstr instr).run js) := by
  sorry

/-- TODO: Docs -/
theorem systemProjectResult_execProgram_eq_projectResult
    (program : JoltISA.Program) (js : SailJoltState)
    (hlinked : LinkedCSRs js)
    (h : program.DoesNotWriteProtectedVRegs) :
    systemProjectResult ((JoltISA.execProgram program).run js) =
      projectResult ((JoltISA.execProgram program).run js) := by
  sorry

end System

end
