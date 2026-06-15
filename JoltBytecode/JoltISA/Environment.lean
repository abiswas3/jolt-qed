import JoltBytecode.Derived

/-!
# Jolt execution environment helpers

This file contains executable Sail memory helpers used to connect Jolt bytecode
proofs to the Sail memory model. Primitive proof assumptions live in
`JoltBytecode.Assumptions`; top-level derived facts from those assumptions live
in `JoltBytecode.Derived`.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Memory read primitives (raw Sail memory access)
-- ============================================================================

-- Read a single byte from Sail's physical memory.
-- At the bottom of Sail's memory hierarchy, readByte looks up addr in
-- state.mem (an ExtHashMap Nat (BitVec 8)). This is the same operation.
def sailReadByte (addr : Nat) : SailM (BitVec 8) := fun s =>
  match s.mem.get? addr with
  | some v => .ok v s
  | none => .error (Error.OutOfMemoryRange addr) s

-- Read 4 bytes (little-endian) from Sail's memory, producing a 32-bit word.
def sailReadWord (addr : BitVec 64) : SailM (BitVec 32) := do
  let b0 ← sailReadByte addr.toNat
  let b1 ← sailReadByte (addr.toNat + 1)
  let b2 ← sailReadByte (addr.toNat + 2)
  let b3 ← sailReadByte (addr.toNat + 3)
  pure (b3 ++ b2 ++ b1 ++ b0)

-- Read 8 bytes (little-endian) from Sail's memory, producing a 64-bit dword.
def sailReadDword (addr : BitVec 64) : SailM (BitVec 64) := do
  let lo ← sailReadWord addr
  let hi ← sailReadWord (addr + 4)
  pure ((hi ++ lo : BitVec 64))

-- ============================================================================
-- Focused bridge lemmas for the vmem_read pipeline
-- ============================================================================

/- STALE:
These two older load-factoring bridge lemmas are not referenced anywhere in the
current instruction-equivalence development. The active load proofs use the
newer local lemmas in `InstructionEquivalence/LoadDefUtils.lean` and the
instruction-specific files instead.

Keeping the old sorried declarations here only pollutes the build status, so
they are commented out until there is a reason to revive them.

theorem translateAddr_machine_bare ...
theorem execute_LOAD_LW_factored ...
-/

-- ============================================================================
-- sail_cases tactic
-- ============================================================================

syntax "sail_cases" term : tactic
macro_rules
  | `(tactic| sail_cases $t:term) => `(tactic|
      (generalize $t = _sc; cases _sc <;> simp))

end
