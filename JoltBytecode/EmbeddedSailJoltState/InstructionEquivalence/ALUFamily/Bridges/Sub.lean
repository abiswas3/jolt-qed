import JoltBytecode.EmbeddedSailJoltState.RegisterOps

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail

noncomputable section

/-!
# Bridge: truncation distributes over subtraction

`(a -₆₄ b)[31:0] = a[31:0] -₃₂ b[31:0]`. Used by `SUBW`.
-/

theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

end
