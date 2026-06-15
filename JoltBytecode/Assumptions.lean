import JoltBytecode.JoltISA.Operands

/-!
# Jolt proof assumptions

This file is the top-level index of primitive assumptions used by the
instruction-equivalence proofs. It is intentionally assumption-only:

* structures and abbreviations state the facts proofs may assume;
* no theorem declarations or derived facts live here;
* composed proof-facing bundles live in family `Bundles` modules;
* exact low-level memory access facts live in
  `InstructionEquivalence.Memory.Utils`;
* projections and derived consequences live in `Derived` or family utility
  files.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Execution assumptions
-- ============================================================================

/-- The current Sail privilege register is Machine mode. -/
structure CurPrivilegeMachine (s : SailState) : Prop where
  value : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)

/-- The Sail `mstatus` register is readable and has MPRV=0. -/
structure MstatusMprvZero (s : SailState) : Prop where
  value : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1

-- ============================================================================
-- Register assumptions
-- ============================================================================

/-- Reading integer register `r` returns `value` without changing Sail state. -/
structure XRegRead (r : regidx) (value : BitVec 64) (s : SailState) : Prop where
  value_eq : rX_bits r s = .ok value s

/-- Integer register `r` is readable, with some value. -/
structure XRegReadable (r : regidx) (s : SailState) : Prop where
  exists_value : ∃ value : BitVec 64, rX_bits r s = .ok value s

-- ============================================================================
-- Memory assumptions
-- ============================================================================

/-- The bytes in `[addr, addr + width)` are present in Sail's finite memory map. -/
structure MemBytesPresent (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  present : ∀ k : Nat, k < width → s.mem.get? (addr.toNat + k) ≠ none

/-- The common 8-byte Jolt memory window is present. -/
abbrev DwordBytesPresent (addr : BitVec 64) (s : SailState) : Prop :=
  MemBytesPresent addr 8 s

/-- Machine-mode PMP accepts a data load from `addr` for `width` bytes. -/
abbrev LoadPmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Load Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every data-load subaccess inside
`[addr, addr + width)`. -/
abbrev LoadPmpOkInRange (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    LoadPmpOk (addr + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts a data store to `addr` for `width` bytes. -/
abbrev StorePmpOk (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s

/-- Machine-mode PMP accepts every data-store subaccess inside
`[addr, addr + width)`. -/
abbrev StorePmpOkInRange (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    StorePmpOk (addr + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts an AMO at `addr` for `width` bytes. -/
abbrev AtomicPmpOk
    (op : amoop) (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

/-- Machine-mode PMP accepts every AMO subaccess inside
`[addr, addr + width)`. -/
abbrev AtomicPmpOkInRange
    (op : amoop) (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    AtomicPmpOk op (addr + BitVec.ofNat 64 offset) accessWidth s

/-- Machine-mode PMP accepts a load-reserved access at `addr`. -/
abbrev LoadReservedPmpOk
    (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  phys_access_check (LoadReserved Data) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s

/-- Machine-mode PMP accepts every load-reserved subaccess inside
`[addr, addr + width)`. -/
abbrev LoadReservedPmpOkInRange
    (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    LoadReservedPmpOk (addr + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not readable MMIO. -/
abbrev NotReadableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s

/-- Every subaccess inside `[addr, addr + width)` is not readable MMIO. -/
abbrev NotReadableMmioInRange (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    NotReadableMmio (addr + BitVec.ofNat 64 offset) accessWidth s

/-- The physical range is not writable MMIO. -/
abbrev NotWritableMmio (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Every subaccess inside `[addr, addr + width)` is not writable MMIO. -/
abbrev NotWritableMmioInRange (addr : BitVec 64) (width : Nat) (s : SailState) : Prop :=
  ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
    NotWritableMmio (addr + BitVec.ofNat 64 offset) accessWidth s

end
