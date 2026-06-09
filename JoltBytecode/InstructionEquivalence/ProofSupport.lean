import JoltBytecode.JoltISA.Semantics.RegisterOps

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
# Instruction equivalence proof support

Shared proof assumptions and small helpers used by instruction-equivalence
files. This module intentionally does not contain mvcgen specs or generic
program closers; concrete instruction proofs should expose the emitted Jolt
instruction sequence directly.
-/

/-- A state is well-formed if every architectural register read succeeds
without changing the Sail state. -/
def WellFormed (js : SailJoltState) : Prop :=
  ∀ r : regidx, ∃ v, rX_bits r js.sail = .ok v js.sail

end
