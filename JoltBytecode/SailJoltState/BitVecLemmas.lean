import JoltBytecode.SailJoltState.Defs

/-!
# BitVec Lemmas

Pure mathematical facts about Sail's BitVec operations, independent of
any monadic or state machinery. These are the "mathematical core" that
instruction correctness proofs reduce to.

- extractLsb_add: truncating to 32 bits distributes over addition
- extractLsb_sub: truncating to 32 bits distributes over subtraction
-/

set_option maxHeartbeats 1_000_000_000

open Sail PreSail LeanRV64D.Functions

noncomputable section

-- Truncating to 32 bits distributes over addition.
-- extractLsb(a + b, 31, 0) = extractLsb(a, 31, 0) + extractLsb(b, 31, 0)
--
-- This is the mathematical core of the ADDW proof: Jolt computes
-- v1 + v2 at 64 bits then truncates, while Sail truncates then adds.
-- Both give the same 32-bit result because addition mod 2^32 doesn't
-- depend on the upper bits.
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

-- Truncating to 32 bits distributes over subtraction.
-- This is the mathematical core of the SUBW proof.
theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

end
