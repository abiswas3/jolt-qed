import LeanRV64D.Prelude

/-!
# Shared memory vocabulary

This file contains pure address expressions used by public assumption bundles
and instruction-equivalence proofs. 
It intentionally contains no assumptions,
memory-state predicates, or proof-collapse lemmas.
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
