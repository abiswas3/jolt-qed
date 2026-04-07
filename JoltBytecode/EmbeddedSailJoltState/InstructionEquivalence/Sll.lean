import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Sll

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SLL: Jolt VirtualPow2 + MUL = Sail SLL

Jolt decomposes SLL as (from BytecodeExpansions/Sll.lean):
1. VirtualPow2 rs2        — compute 2^(rs2[5:0])
2. MUL rd, rs1, pow       — multiply rs1 by 2^shift (= left shift)

Multiplying by 2^s equals left-shifting by s.
Sail's SLL does shift_bits_left v1 (extractLsb v2 5 0).
-/

-- Bridge: Jolt's multiply by 2^(rs2[5:0]) = Sail's shift_bits_left.
-- rs1 * 2^(rs2[5:0]) = shift_bits_left rs1 (extractLsb rs2 5 0).
private lemma sll_mul_eq_shift (v1 v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  sorry

-- Factoring: execute_RTYPE SLL reads rs1, rs2, left-shifts v1 by v2[5:0].
private theorem execute_RTYPE_SLL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  sorry

-- Jolt's SLL: read rs1, read rs2, compute 2^(rs2[5:0]), multiply, write to rd.
def jolt_sll (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  let v_pow := BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)
  liftSail (wX_bits rd (v1 * v_pow))
  pure RETIRE_SUCCESS

-- Running Jolt's SLL and projecting equals running Sail's SLL.
theorem jolt_sll_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sll rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail := by
  rw [execute_RTYPE_SLL_factored]
  unfold jolt_sll liftSail projectResult
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  rw [sll_mul_eq_shift v1 v2]
  cases wX_bits rd _ js.sail with
  | error e s => simp [project]
  | ok a s => simp [project]

end
