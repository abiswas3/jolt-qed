import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.Memory.Utils

/-!
# Atomic-family shared theorem assumptions

Shared memory and translation assumptions for the RV64 AMO equivalence
statements.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

structure StoreIdentityTranslation (addr : BitVec 64) (s : SailState) : Prop where
  translate : translateAddr (Virtaddr addr) (Store Data) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

structure FlatStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  pmp : phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  mmio : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

structure AtomicIdentityTranslation (op : amoop) (addr : BitVec 64)
    (s : SailState) : Prop where
  translate : translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

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
  jolt_load_mem : FlatPhysMem joltAddr 8 s
  jolt_store_translate : StoreIdentityTranslation joltAddr s
  jolt_store_mem : FlatStoreMem joltAddr 8 s
  sail_atomic_translate : AtomicIdentityTranslation op amoAddr s
  sail_atomic_mem : FlatAtomicMem op amoAddr sailWidth s

end AtomicFamily

end
