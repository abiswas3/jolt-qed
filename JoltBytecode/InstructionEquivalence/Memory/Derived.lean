import JoltBytecode.InstructionEquivalence.Memory.Utils
import Mathlib.Tactic

/-!
# Derived exact flat-memory access facts

This file contains generic consequences of primitive memory facts and the
exact flat-memory predicates in `Memory.Utils`. It is intentionally family-agnostic:
there are no `LoadFamily`, `StoreFamily`, `AtomicFamily`, or
`LoadReservedFamily` structures here.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Assumptions.DwordPresent

/-- The primitive dword-present assumption gives the byte-present helper for
the whole 8-byte dword. -/
theorem memBytesPresent
    {addr : BitVec 64} {s : SailState}
    (h : Assumptions.DwordPresent addr s) :
    MemBytesPresent addr 8 s := by
  rcases h.bytes with ⟨bytes, hbytes⟩
  refine ⟨fun k hk => ?_⟩
  have hget := hbytes ⟨k, hk⟩
  rw [hget]
  simp

end Assumptions.DwordPresent

namespace MemBytesPresent

/-- Byte-present facts are monotone over explicit subwindows. -/
theorem subaccess
    {base : BitVec 64} {baseWidth offset accessWidth : Nat} {s : SailState}
    (hbytes : MemBytesPresent base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    MemBytesPresent (base + BitVec.ofNat 64 offset) accessWidth s := by
  refine ⟨fun k hk => ?_⟩
  have hoff64 : offset < 2 ^ 64 := by
    omega
  have hoff_toNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hoff64
  have haddr_toNat :
      (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset := by
    rw [BitVec.toNat_add_of_lt]
    · rw [hoff_toNat]
    · rw [hoff_toNat]
      exact h_no_ovf
  have hbase := hbytes.present (offset + k) (by omega)
  simpa [haddr_toNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbase

end MemBytesPresent

namespace FlatPhysMem

/-- A read window whose PMP/MMIO assumptions cover all subaccesses gives the
exact read-memory fact for any explicit subwindow. -/
theorem ofReadWindowSubaccess
    (base : BitVec 64) (baseWidth offset accessWidth : Nat) (s : SailState)
    (hbytes : MemBytesPresent base baseWidth s)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hmmio :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    FlatPhysMem (base + BitVec.ofNat 64 offset) accessWidth s :=
  { bytes := MemBytesPresent.subaccess hbytes hfits h_no_ovf
    pmp := hpmp offset accessWidth hfits
    mmio := hmmio offset accessWidth hfits }

/-- The whole read window is also an exact read-memory fact. -/
theorem ofReadWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hmmio :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s) :
    FlatPhysMem base width s := by
  have h := ofReadWindowSubaccess base width 0 width s
    hbytes hpmp hmmio (by omega) (by exact base.isLt)
  simpa using h

end FlatPhysMem

namespace FlatStoreMem

/-- A write window whose PMP/MMIO assumptions cover all subaccesses gives the
exact write-memory fact for any explicit subwindow. -/
theorem ofWriteWindowSubaccess
    (base : BitVec 64) (baseWidth offset accessWidth : Nat) (s : SailState)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hmmio :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    FlatStoreMem (base + BitVec.ofNat 64 offset) accessWidth s :=
  { pmp := hpmp offset accessWidth hfits
    mmio := hmmio offset accessWidth hfits }

/-- The whole write window is also an exact write-memory fact. -/
theorem ofWriteWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hmmio :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s) :
    FlatStoreMem base width s := by
  have h := ofWriteWindowSubaccess base width 0 width s
    hpmp hmmio (by omega)
  simpa using h

end FlatStoreMem

namespace FlatLoadStoreMem

theorem ofReadWriteWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hloadPmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        LoadPmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hstorePmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        StorePmpOk (base + BitVec.ofNat 64 offset) accessWidth s)
    (hreadable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hwritable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s) :
    FlatLoadStoreMem base width s :=
  { bytes := hbytes
    load_pmp := by simpa using hloadPmp 0 width (by omega)
    store_pmp := by simpa using hstorePmp 0 width (by omega)
    readable := by simpa using hreadable 0 width (by omega)
    writable := by simpa using hwritable 0 width (by omega) }

end FlatLoadStoreMem

namespace FlatAtomicMem

/-- An atomic window whose PMP/MMIO assumptions cover all subaccesses gives the
exact atomic-memory fact for any explicit subwindow. -/
theorem ofAtomicWindowSubaccess
    (op : amoop) (base : BitVec 64) (baseWidth offset accessWidth : Nat)
    (s : SailState)
    (hbytes : MemBytesPresent base baseWidth s)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s)
    (hreadable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hwritable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ baseWidth →
        NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    FlatAtomicMem op (base + BitVec.ofNat 64 offset) accessWidth s :=
  { bytes := MemBytesPresent.subaccess hbytes hfits h_no_ovf
    pmp := hpmp offset accessWidth hfits
    readable := hreadable offset accessWidth hfits
    writable := hwritable offset accessWidth hfits }

/-- The whole atomic window is also an exact atomic-memory fact. -/
theorem ofAtomicWindow
    (op : amoop) (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hpmp :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        AtomicPmpOk op (base + BitVec.ofNat 64 offset) accessWidth s)
    (hreadable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotReadableMmio (base + BitVec.ofNat 64 offset) accessWidth s)
    (hwritable :
      ∀ offset accessWidth : Nat, offset + accessWidth ≤ width →
        NotWritableMmio (base + BitVec.ofNat 64 offset) accessWidth s) :
    FlatAtomicMem op base width s := by
  have h := ofAtomicWindowSubaccess op base width 0 width s
    hbytes hpmp hreadable hwritable (by omega) (by exact base.isLt)
  simpa using h

end FlatAtomicMem

end
