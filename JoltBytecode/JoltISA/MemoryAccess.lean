import LeanRV64D.Prelude

/-!
# Jolt ISA memory address vocabulary

Pure address expressions used by public assumption bundles and instruction-
equivalence proofs.  This file is the memory analogue of `RegisterAccess.lean`'s
address layer: it contains no assumptions, memory-state predicates, or
proof-collapse lemmas.

The `Memory` namespace holds the canonical names.  The top-level compatibility
abbrevs below (`aligned_dword_addr`, `load_effective_address`,
`compute_aligned_dword_base_address`) preserve the legacy spellings used by
existing load/store proofs.

Phase 2 of the memory-access cleanup will introduce `memRead`/`memWrite`
helpers wrapping `liftSail (vmem_*_addr …)` and rewire `execInstr`'s `LD`/`SD`
to use them.  That step touches the load/store proof theory and is deliberately
scoped separately from this address-vocabulary consolidation.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Memory

/-- Effective address for base-plus-12-bit-immediate memory instructions. -/
abbrev effectiveAddr12 (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  base + sign_extend (m := 64) imm

/-- Align an address down to the enclosing 8-byte dword. -/
abbrev dwordBase (addr : BitVec 64) : BitVec 64 :=
  addr &&& (-8 : BitVec 64)

/-- Enclosing dword base for base-plus-12-bit-immediate memory instructions. -/
abbrev effectiveDwordBase12 (base : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  dwordBase (effectiveAddr12 base imm)

end Memory

/-! Compatibility names used by existing load/store proofs. -/

/-- Common aligned dword address used by the Jolt inline load sequences:
compute the effective address, align it down to an 8-byte boundary, then use
zero offset for the actual `LD`. -/
abbrev aligned_dword_addr (v : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  (v + sign_extend (m := 64) imm) &&& sign_extend (m := 64) (-8 : BitVec 12)

/-- Generic effective address for memory instructions with a sign-extended
12-bit immediate. -/
abbrev load_effective_address (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  Memory.effectiveAddr12 val imm

/-- Generic aligned dword base address used by the Jolt inline memory sequences
after computing the effective address. -/
abbrev compute_aligned_dword_base_address
    (val : BitVec 64) (imm : BitVec 12) : BitVec 64 :=
  load_effective_address val imm &&& (-8 : BitVec 64)

end
