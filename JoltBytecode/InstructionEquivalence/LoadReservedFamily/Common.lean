import JoltBytecode.JoltISA.Expansions.LoadReserved
import JoltBytecode.InstructionEquivalence.LoadDefUtils

/-!
# Load-reserved shared helpers

LR proofs have a different memory shape from ordinary loads. The Jolt expansion
uses ordinary load bytecode, while Sail executes a `LoadReserved Data` memory
access. This module is the home for shared LR helper definitions.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadReservedFamily

/-- Internal memory context shared by load-reserved helper lemmas.

This is not a public theorem assumption. A final public LR theorem should use a
primitive-assumption bundle and derive this context internally. -/
structure LoadReservedMemoryContext
    (sailWidth : Nat) (joltAddr lrAddr : BitVec 64)
    (s : SailState) : Prop where
  jolt_load_mem : FlatPhysMem joltAddr 8 s
  cfg : JoltConfig s

/-- The ordinary Jolt read used by the LR expansion. -/
theorem LoadReservedMemoryContext.jolt_load
    {sailWidth : Nat} {joltAddr lrAddr : BitVec 64} {s : SailState}
    (h : LoadReservedMemoryContext sailWidth joltAddr lrAddr s) :
    FlatPhysMem joltAddr 8 s :=
  h.jolt_load_mem

end LoadReservedFamily

end
