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

-- Step 1: setWidth 6 = extractLsb 5 0 (both extract the lower 6 bits)
private lemma setWidth_eq_extractLsb (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v (LeanRV64D.Functions.log2_xlen -i 1) 0 := by
  unfold LeanRV64D.Functions.log2_xlen Sail.BitVec.extractLsb
  ext i
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]

-- Step 2: multiplying by 2^n = left shift by n (for BitVec)
private lemma mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

-- Bridge: Jolt's multiply by 2^(rs2[5:0]) = Sail's shift_bits_left.
private lemma sll_mul_eq_shift (v1 v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [← setWidth_eq_extractLsb]
  exact mul_pow2_eq_shiftLeft v1 (v2.setWidth 6)

-- Jolt's SLL: read rs1, read rs2, compute 2^(rs2[5:0]), multiply, write to rd.
def jolt_sll (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  let v_pow := BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)
  liftSail (wX_bits rd (v1 * v_pow))
  pure RETIRE_SUCCESS

-- Factoring: execute_RTYPE SLL reads rs1, rs2, left-shifts v1 by v2[5:0].
private theorem execute_RTYPE_SLL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

-- Concrete: characterise what jolt_sll writes to rd.
theorem jolt_sll_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sll rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)) := by
  unfold jolt_sll liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  obtain ⟨s', hw⟩ := wX_shape rd (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)) js.sail
  simp only [hw]
  exact ⟨_, v1, v2, rfl, rfl, rfl, wX_bits_eq_stateAfterWrite rd _ js.sail s' hw⟩

-- Running Jolt's SLL and projecting equals running Sail's SLL.
theorem jolt_sll_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sll rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_sll_concrete rs2 rs1 rd js hwf
  rw [execute_RTYPE_SLL_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_sll rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail, sll_mul_eq_shift v1 v2]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
