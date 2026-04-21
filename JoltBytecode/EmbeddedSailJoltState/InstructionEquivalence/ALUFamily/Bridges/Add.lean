import JoltBytecode.EmbeddedSailJoltState.RegisterOps

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail

noncomputable section

/-!
# Bridge: truncation distributes over addition

Pure `BitVec` math, no state monad. This bridge lemma is used by every
ALU W-variant addition instruction: `ADDW` (R-type W) and `ADDIW`
(I-type W). In both cases Jolt computes the full-width sum and then
truncates, while Sail truncates first and adds. These agree because
addition mod `2 ^ 32` does not depend on bits above the 32-bit boundary.
-/

/-- `(a +₆₄ b)[31:0] = a[31:0] +₃₂ b[31:0]`. -/
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

end
