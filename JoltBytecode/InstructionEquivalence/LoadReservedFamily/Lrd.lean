import JoltBytecode.InstructionEquivalence.LoadReservedFamily.Common

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace LoadReservedFamily

/-!
# LR.D top-level equivalence statement

This file intentionally only states the public theorem. The proof should reduce
the Rust-faithful Jolt trace into the reservation-register prefix and the final
ordinary `LD`, then bridge that ordinary load to Sail's reserved-load access.
-/

/-- Main public theorem for `LR.D`.

The theorem has no explicit alignment or overflow hypothesis. The proof will
case on dword alignment and derive the aligned-path arithmetic facts locally.
The Jolt program includes the Rust writes to both reservation registers before
the final `LD` row. -/
theorem lrdProgram_eq_sail
    (rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : LoadReservedMemoryAssumptions 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.lrdProgram rs1 rd)).run js) =
      (execute_LOADRES false false rs1 8 rd).run js.sail := by
  sorry

end LoadReservedFamily

end
