import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.Memory.Utils

/-!
# Atomic-family shared memory helpers

Shared memory helper facts for RV64 AMO equivalence proofs.

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

/-- Internal memory context shared by AMO helper lemmas.

This is not a public theorem assumption. Public AMO theorems take
`AmoDwordProgramEqSailAssumptions` or `AmoWordProgramEqSailAssumptions`;
`AtomicFamily.Derived` constructs this context from those public bundles. -/
structure AmoMemoryContext
    (op : amoop) (sailWidth : Nat) (joltAddr amoAddr : BitVec 64)
    (s : SailState) : Prop where
  jolt_mem : FlatLoadStoreMem joltAddr 8 s
  sail_atomic_mem : FlatAtomicMem op amoAddr sailWidth s
  cfg : JoltConfig s

theorem AmoMemoryContext.jolt_load_mem
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (h : AmoMemoryContext op sailWidth joltAddr amoAddr s) :
    FlatPhysMem joltAddr 8 s :=
  h.jolt_mem.toFlatPhysMem

theorem AmoMemoryContext.jolt_store_mem
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (h : AmoMemoryContext op sailWidth joltAddr amoAddr s) :
    FlatStoreMem joltAddr 8 s :=
  h.jolt_mem.toFlatStoreMem

theorem AmoMemoryContext.jolt_bytes
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (h : AmoMemoryContext op sailWidth joltAddr amoAddr s) :
    DwordBytesPresent joltAddr s :=
  h.jolt_mem.bytes

theorem AmoMemoryContext.jolt_store_translate
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (_h_mem : AmoMemoryContext op sailWidth joltAddr amoAddr s)
    (hcfg : JoltConfig s) :
    translateAddr (Virtaddr joltAddr) (Store Data) s =
      .ok (Ok (physaddr.Physaddr joltAddr, init_ext_ptw)) s :=
  translateAddr_store_data_of_joltConfig joltAddr s hcfg

theorem AmoMemoryContext.sail_atomic_translate
    {op : amoop} {sailWidth : Nat} {joltAddr amoAddr : BitVec 64}
    {s : SailState} (_h_mem : AmoMemoryContext op sailWidth joltAddr amoAddr s)
    (hcfg : JoltConfig s) :
    translateAddr (Virtaddr amoAddr) (Atomic (op, Data, Data)) s =
      .ok (Ok (physaddr.Physaddr amoAddr, init_ext_ptw)) s :=
  translateAddr_atomic_data_of_joltConfig op amoAddr s hcfg

end AtomicFamily

end
