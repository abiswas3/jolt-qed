import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.Memory.Utils

/-!
# Atomic-family shared theorem assumptions

Shared memory-shape assumptions for the RV64 AMO equivalence statements.

Address translation is intentionally not part of this bundle. Under
`JoltConfig`, normal store and data-AMO translations reduce to bare identity via
`translateAddr_store_data_of_joltConfig` and
`translateAddr_atomic_data_of_joltConfig`.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

structure FlatStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  pmp : phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  mmio : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

/-- Ordinary RAM access for the Jolt-side load/store pair used by AMO
expansions. The public AMO assumption should say this once; projections below
adapt it to the existing load and store helper APIs. -/
structure FlatLoadStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  load_pmp : phys_access_check (Load Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  store_pmp : phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  readable : within_mmio_readable (physaddr.Physaddr addr) width s =
    .ok false s
  writable : within_mmio_writable (physaddr.Physaddr addr) width s =
    .ok false s

theorem FlatLoadStoreMem.toFlatPhysMem
    {addr : BitVec 64} {width : Nat} {s : SailState}
    (h : FlatLoadStoreMem addr width s) :
    FlatPhysMem addr width s :=
  { pmp := h.load_pmp
    mmio := h.readable }

theorem FlatLoadStoreMem.toFlatStoreMem
    {addr : BitVec 64} {width : Nat} {s : SailState}
    (h : FlatLoadStoreMem addr width s) :
    FlatStoreMem addr width s :=
  { pmp := h.store_pmp
    mmio := h.writable }

structure FlatAtomicMem (op : amoop) (addr : BitVec 64) (width : Nat)
    (s : SailState) : Prop where
  pmp : phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s
  readable : within_mmio_readable (physaddr.Physaddr addr) width s =
    .ok false s
  writable : within_mmio_writable (physaddr.Physaddr addr) width s =
    .ok false s

structure AmoMemoryAssumptions
    (op : amoop) (sailWidth : Nat) (joltAddr amoAddr : BitVec 64)
    (s : SailState) : Prop where
  jolt_mem : FlatLoadStoreMem joltAddr 8 s
  sail_atomic_mem : FlatAtomicMem op amoAddr sailWidth s

theorem AmoMemoryAssumptions.jolt_load_mem
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (h_mem : AmoMemoryAssumptions op sailWidth joltAddr amoAddr s) :
    FlatPhysMem joltAddr 8 s :=
  h_mem.jolt_mem.toFlatPhysMem

theorem AmoMemoryAssumptions.jolt_store_mem
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (h_mem : AmoMemoryAssumptions op sailWidth joltAddr amoAddr s) :
    FlatStoreMem joltAddr 8 s :=
  h_mem.jolt_mem.toFlatStoreMem

theorem AmoMemoryAssumptions.jolt_store_translate
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (_h_mem : AmoMemoryAssumptions op sailWidth joltAddr amoAddr s)
    (hcfg : JoltConfig s) :
    translateAddr (Virtaddr joltAddr) (Store Data) s =
      .ok (Ok (physaddr.Physaddr joltAddr, init_ext_ptw)) s :=
  translateAddr_store_data_of_joltConfig joltAddr s hcfg

theorem AmoMemoryAssumptions.sail_atomic_translate
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (_h_mem : AmoMemoryAssumptions op sailWidth joltAddr amoAddr s)
    (hcfg : JoltConfig s) :
    translateAddr (Virtaddr amoAddr) (Atomic (op, Data, Data)) s =
      .ok (Ok (physaddr.Physaddr amoAddr, init_ext_ptw)) s :=
  translateAddr_atomic_data_of_joltConfig op amoAddr s hcfg

end AtomicFamily

end
