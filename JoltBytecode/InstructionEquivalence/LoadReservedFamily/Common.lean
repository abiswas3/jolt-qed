import JoltBytecode.JoltISA.Expansions.LoadReserved
import JoltBytecode.InstructionEquivalence.LoadDefUtils

/-!
# Load-reserved shared theorem assumptions

LR proofs have a different memory shape from ordinary loads. The Jolt expansion
uses ordinary load bytecode, while Sail executes a `LoadReserved Data` memory
access. This file packages those two views once so the `LR.W` and `LR.D`
statements do not grow parallel lists of low-level memory hypotheses.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LoadReservedFamily

/-- Ordinary RAM access for Sail's reserved-load read. -/
structure FlatLoadReservedMem (addr : BitVec 64) (width : Nat)
    (s : SailState) : Prop where
  pmp : phys_access_check (LoadReserved Data) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s
  readable : within_mmio_readable (physaddr.Physaddr addr) width s =
    .ok false s

/-- Shared LR memory envelope.

`joltAddr` is the address read by the Jolt bytecode. For `LR.W` this is the
containing aligned dword; for `LR.D` it is the LR address itself. `lrAddr` is
the architectural address used by Sail's reserved load. -/
structure LoadReservedMemoryAssumptions
    (sailWidth : Nat) (joltAddr lrAddr : BitVec 64)
    (s : SailState) : Prop where
  jolt_load_mem : FlatPhysMem joltAddr 8 s
  sail_reserved_mem : FlatLoadReservedMem lrAddr sailWidth s

/-- Project the Jolt-side ordinary load memory assumption out of the LR
envelope. -/
theorem LoadReservedMemoryAssumptions.jolt_load
    {sailWidth : Nat} {joltAddr lrAddr : BitVec 64} {s : SailState}
    (h_mem : LoadReservedMemoryAssumptions sailWidth joltAddr lrAddr s) :
    FlatPhysMem joltAddr 8 s :=
  h_mem.jolt_load_mem

/-- Project the Sail-side reserved-load memory assumption out of the LR
envelope. -/
theorem LoadReservedMemoryAssumptions.sail_reserved
    {sailWidth : Nat} {joltAddr lrAddr : BitVec 64} {s : SailState}
    (h_mem : LoadReservedMemoryAssumptions sailWidth joltAddr lrAddr s) :
    FlatLoadReservedMem lrAddr sailWidth s :=
  h_mem.sail_reserved_mem

end LoadReservedFamily

end
