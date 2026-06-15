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
    (hpmp : LoadPmpOkInRange base baseWidth s)
    (hmmio : NotReadableMmioInRange base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    FlatPhysMem (base + BitVec.ofNat 64 offset) accessWidth s :=
  { bytes := hbytes.subaccess hfits h_no_ovf
    pmp := hpmp offset accessWidth hfits
    mmio := hmmio offset accessWidth hfits }

/-- The whole read window is also an exact read-memory fact. -/
theorem ofReadWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hpmp : LoadPmpOkInRange base width s)
    (hmmio : NotReadableMmioInRange base width s) :
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
    (hpmp : StorePmpOkInRange base baseWidth s)
    (hmmio : NotWritableMmioInRange base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth) :
    FlatStoreMem (base + BitVec.ofNat 64 offset) accessWidth s :=
  { pmp := hpmp offset accessWidth hfits
    mmio := hmmio offset accessWidth hfits }

/-- The whole write window is also an exact write-memory fact. -/
theorem ofWriteWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hpmp : StorePmpOkInRange base width s)
    (hmmio : NotWritableMmioInRange base width s) :
    FlatStoreMem base width s := by
  have h := ofWriteWindowSubaccess base width 0 width s
    hpmp hmmio (by omega)
  simpa using h

end FlatStoreMem

namespace FlatLoadStoreMem

theorem ofReadWriteWindow
    (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hloadPmp : LoadPmpOkInRange base width s)
    (hstorePmp : StorePmpOkInRange base width s)
    (hreadable : NotReadableMmioInRange base width s)
    (hwritable : NotWritableMmioInRange base width s) :
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
    (hpmp : AtomicPmpOkInRange op base baseWidth s)
    (hreadable : NotReadableMmioInRange base baseWidth s)
    (hwritable : NotWritableMmioInRange base baseWidth s)
    (hfits : offset + accessWidth ≤ baseWidth)
    (h_no_ovf : base.toNat + offset < 2 ^ 64) :
    FlatAtomicMem op (base + BitVec.ofNat 64 offset) accessWidth s :=
  { bytes := hbytes.subaccess hfits h_no_ovf
    pmp := hpmp offset accessWidth hfits
    readable := hreadable offset accessWidth hfits
    writable := hwritable offset accessWidth hfits }

/-- The whole atomic window is also an exact atomic-memory fact. -/
theorem ofAtomicWindow
    (op : amoop) (base : BitVec 64) (width : Nat) (s : SailState)
    (hbytes : MemBytesPresent base width s)
    (hpmp : AtomicPmpOkInRange op base width s)
    (hreadable : NotReadableMmioInRange base width s)
    (hwritable : NotWritableMmioInRange base width s) :
    FlatAtomicMem op base width s := by
  have h := ofAtomicWindowSubaccess op base width 0 width s
    hbytes hpmp hreadable hwritable (by omega) (by exact base.isLt)
  simpa using h

end FlatAtomicMem

end
