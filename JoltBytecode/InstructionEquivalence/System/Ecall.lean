import JoltBytecode.JoltISA.Expansions.System

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# ECALL system expansion

The Rust expansion writes the machine-mode trap fields into reserved virtual
registers and jumps to the virtual `mtvec` register. This statement is the
current review target; the proof will need the system/trap envelope that
relates Sail's `Trap` result to Jolt's ZeroOS trampoline state.
-/

theorem ecallProgram_eq_sail
    (js : SailJoltState) :
    projectResult ((JoltISA.execProgram JoltISA.ecallProgram).run js) =
      (execute_ECALL ()).run js.sail := by
  sorry

end System

end
