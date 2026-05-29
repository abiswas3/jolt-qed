import JoltBytecode.InstructionEquivalence.LoadReservedFamily.Common

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace LoadReservedFamily

/-!
# LR.W top-level equivalence statement

This file intentionally only states the public theorem. The proof will later
split the Rust-faithful Jolt trace into the reservation-register prefix, the
ordinary `LW` load tail, and the bridge from Sail's reserved-load RAM read to
the ordinary Jolt load read.
-/

/-- Main public theorem for `LR.W`.

The theorem has no explicit alignment or overflow hypothesis. The alignment
case split belongs inside the proof, as in the load and atomic families. The
Jolt program includes the Rust reservation-register writes before the `LW`
tail. -/
theorem lrwProgram_eq_sail
    (rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : LoadReservedMemoryAssumptions 4
      (addr &&& (-8 : BitVec 64)) addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.lrwProgram rs1 rd)).run js) =
      (execute_LOADRES false false rs1 4 rd).run js.sail := by
  sorry

end LoadReservedFamily

end
