import JoltBytecode.JoltISA.VirtualRegisters

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-- TODO: Docs -/
def systemProject (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      ((((((js.sail.regs
        |>.insert Register.mtvec (js.vregs JoltISA.trapHandlerVReg))
        |>.insert Register.mscratch (js.vregs JoltISA.mscratchVReg))
        |>.insert Register.mepc (js.vregs JoltISA.mepcVReg))
        |>.insert Register.mcause (js.vregs JoltISA.mcauseVReg))
        |>.insert Register.mtval (js.vregs JoltISA.mtvalVReg))
        |>.insert Register.mstatus (js.vregs JoltISA.mstatusVReg)) }

/-- TODO: Docs -/
def systemProjectResult
    (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (systemProject js')
  | .error e js' => .error e (systemProject js')

end System

end
