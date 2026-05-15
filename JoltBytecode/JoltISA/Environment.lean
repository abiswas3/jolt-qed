import JoltBytecode.JoltISA.Operands

/-!
# Jolt execution environment assumptions

This file contains the Sail memory helpers and state predicates used to connect
Jolt bytecode proofs to the Sail memory model. Core Jolt state and operand
definitions live in `JoltISA.Core` and `JoltISA.Operands`.
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

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
-- JoltConfig: Sail state assumptions for Jolt's execution environment
-- ============================================================================

-- Jolt runs in bare-metal M-mode with flat physical memory. Under these
-- assumptions, Sail's virtual memory pipeline (vmem_read) reduces to raw
-- byte reads from state.mem.
--
-- The conditions are:
-- 1. Machine mode with MPRV=0: translateAddr returns identity (Bare mode)
-- 2. PMP entries are unlocked: Machine mode bypasses PMP
-- 3. Valid PMA region: the physical address has readable attributes
-- 4. Not MMIO: the address is regular RAM, not memory-mapped I/O
-- 5. Memory is populated: all accessed addresses are in state.mem
--
-- These are captured as a predicate on SailState rather than baking in
-- specific register values, so the proofs stay abstract.
structure JoltConfig (s : SailState) : Prop where
  -- Machine mode: cur_privilege register is Machine.
  -- This makes translateAddr use Bare (identity) translation.
  machine_mode : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)
  -- mstatus register is readable and has MPRV=0.
  -- MPRV=0 means effectivePrivilege returns the actual privilege (Machine),
  -- not the MPP field. This ensures Bare translation mode.
  mstatus_ok : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1
  -- All memory addresses are populated in state.mem.
  -- This makes sailReadByte succeed for any address.
  mem_populated : ∀ addr : Nat, s.mem.get? addr ≠ none

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
