import JoltBytecode.EmbeddedSailJoltState.Defs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
# Memory utilities: direct hash-map byte assembly from `SailState.mem`.

These helpers skip Sail's vmem pipeline and read bytes straight from the
state's memory hash map. They are used to describe the intended effect of
memory-touching Jolt instructions in terms that are easy to reason about,
and are related back to Sail's pipeline via bridge theorems elsewhere.
-/

-- The 8-bit byte at a given vaddr. Direct hash-map lookup on `s.mem`.
-- WARNING: returns `0` when vaddr is not populated. Indistinguishable from
-- a legitimately-stored `0`. Callers must carry a populatedness hypothesis
-- (e.g. `JoltConfig.mem_populated`) to rule out the default branch.
def loaded_byte_at (s : SailState) (vaddr : BitVec 64) : BitVec 8 :=
  (s.mem.get? vaddr.toNat).getD 0

-- Explicit little-endian byte-assembly at standard RISC-V load widths.
-- Byte at `vaddr` occupies the low 8 bits; each successive byte stacks above.
-- No recursion, no dependent-type gymnastics — each definition is a plain
-- chain of `BitVec.append` (`++`) of `loaded_byte_at` calls.

def loaded_halfword_at (s : SailState) (vaddr : BitVec 64) : BitVec 16 :=
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

def loaded_word_at (s : SailState) (vaddr : BitVec 64) : BitVec 32 :=
  loaded_byte_at s (vaddr + 3) ++
  loaded_byte_at s (vaddr + 2) ++
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

def loaded_dword_at (s : SailState) (vaddr : BitVec 64) : BitVec 64 :=
  loaded_byte_at s (vaddr + 7) ++
  loaded_byte_at s (vaddr + 6) ++
  loaded_byte_at s (vaddr + 5) ++
  loaded_byte_at s (vaddr + 4) ++
  loaded_byte_at s (vaddr + 3) ++
  loaded_byte_at s (vaddr + 2) ++
  loaded_byte_at s (vaddr + 1) ++
  loaded_byte_at s vaddr

end
