import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.JoltISA.RegisterAccess

/-!
# System-instruction proof helpers

Small facts about the virtual-register layout used by Jolt's system-instruction
expansions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

theorem mstatusVReg_writable :
    WritableVReg JoltISA.mstatusVReg := by
  unfold JoltISA.mstatusVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

theorem mtvecVReg_writable :
    WritableVReg JoltISA.trapHandlerVReg := by
  unfold JoltISA.trapHandlerVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

theorem mscratchVReg_writable :
    WritableVReg JoltISA.mscratchVReg := by
  unfold JoltISA.mscratchVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

theorem mepcVReg_writable :
    WritableVReg JoltISA.mepcVReg := by
  unfold JoltISA.mepcVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

theorem mcauseVReg_writable :
    WritableVReg JoltISA.mcauseVReg := by
  unfold JoltISA.mcauseVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

theorem mtvalVReg_writable :
    WritableVReg JoltISA.mtvalVReg := by
  unfold JoltISA.mtvalVReg WritableVReg JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount
  decide

end System

end
