import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Jolt-to-Sail projection

`project2` is the experimental full projection from Jolt machine state to the
generated Sail state.  Unlike the old plain `project`, it materializes the
persistent Jolt CSR virtual registers into the generated Sail CSR register map
before discarding the virtual-register file.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Project Jolt state to Sail state, materializing persistent CSR virtual
registers as their generated Sail CSR registers. -/
def project2 (js : SailJoltState) : SailState :=
  { js.sail with
    regs :=
      ((((((js.sail.regs
        |>.insert Register.mtvec (js.vregs trapHandlerVReg))
        |>.insert Register.mscratch (js.vregs mscratchVReg))
        |>.insert Register.mepc (js.vregs mepcVReg))
        |>.insert Register.mcause (js.vregs mcauseVReg))
        |>.insert Register.mtval (js.vregs mtvalVReg))
        |>.insert Register.mstatus (js.vregs mstatusVReg)) }

/-- Project a Jolt run result through `project2`, preserving result and error
shape. -/
def projectResult2
    (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project2 js')
  | .error e js' => .error e (project2 js')

end JoltISA

end
