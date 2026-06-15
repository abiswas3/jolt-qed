import JoltBytecode.Assumptions

/-!
# Jolt proof bundles

Bundles package primitive assumptions from `JoltBytecode.Assumptions`. They do
not introduce new primitive assumptions and contain no theorem declarations.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Execution bundles
-- ============================================================================

/-- Global execution configuration needed by the Sail/Jolt equivalence proofs.

This is a bundle of primitive register-state assumptions. Bare translation is a
derived theorem from this bundle, not an assumption. -/
structure JoltConfig (s : SailState) : Prop where
  cur_privilege : CurPrivilegeMachine s
  mstatus_mprv : MstatusMprvZero s

-- ============================================================================
-- Memory-window bundles
-- ============================================================================

/-- Primitive assumptions for one 8-byte readable dword window.

This is used by Jolt expansions that read an enclosing dword and then derive
smaller Sail reads from that window. -/
structure DwordReadWindowAssumptions (base : BitVec 64) (s : SailState) :
    Prop where
  bytes : MemBytesPresent base 8 s
  load_pmp : LoadPmpOkInRange base 8 s
  not_readable_mmio : NotReadableMmioInRange base 8 s

/-- Primitive assumptions for one 8-byte dword window that Jolt both reads and
writes.

This is used by Jolt store-style expansions that load the enclosing dword,
splice a narrower value, and store the enclosing dword back. -/
structure DwordReadWriteWindowAssumptions (base : BitVec 64) (s : SailState) :
    Prop extends DwordReadWindowAssumptions base s where
  store_pmp : StorePmpOkInRange base 8 s
  not_writable_mmio : NotWritableMmioInRange base 8 s

/-- Primitive assumptions for one 8-byte AMO/Jolt memory window.

The `base` parameter is the important address: `.D` AMOs use the architectural
address, while `.W` AMOs use the enclosing aligned dword base. -/
structure AmoDwordWindowAssumptions
    (op : amoop) (base : BitVec 64) (s : SailState) :
    Prop extends DwordReadWriteWindowAssumptions base s where
  atomic_pmp : AtomicPmpOkInRange op base 8 s

end
