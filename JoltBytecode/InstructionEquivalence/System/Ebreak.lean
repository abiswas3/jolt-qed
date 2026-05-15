import JoltBytecode.JoltISA.Expansions.System

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-!
# EBREAK system expansion

The Rust expansion emits `JAL scratch, 0`, which keeps the PC fixed so the
emulator treats the instruction as program termination. This statement is
sorried for review because raw Sail `execute_EBREAK` returns a breakpoint trap,
so the final proof may need a termination-specific relation rather than plain
state equality.
-/

theorem ebreakProgram_eq_sail
    (js : SailJoltState) :
    projectResult ((JoltISA.execProgram JoltISA.ebreakProgram).run js) =
      (execute_EBREAK ()).run js.sail := by
  sorry

end System

end
