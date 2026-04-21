import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Family

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLL: Jolt VirtualPow2 + MUL = Sail SLL

Jolt decomposes SLL as (from `BytecodeExpansions/Sll.lean`):
1. `VirtualPow2 rs2 → v_pow` — compute `2^(rs2[5:0])`
2. `MUL rd, rs1, v_pow` — multiply by power of two (= left shift)

Multiply-by-`2^s` = left-shift-by-`s`; the bridge fact is inlined here
because it is SLL-specific (not shared with other shift instructions).
-/

private theorem setWidth_eq_extractLsb (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v (LeanRV64D.Functions.log2_xlen -i 1) 0 := by
  unfold LeanRV64D.Functions.log2_xlen Sail.BitVec.extractLsb
  ext i
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb]

private theorem mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem sll_mul_eq_shift (v1 v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [← setWidth_eq_extractLsb]
  exact mul_pow2_eq_shiftLeft v1 (v2.setWidth 6)

theorem execute_RTYPE_SLL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

def jolt_sll (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  let v_pow := BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)
  liftSail (wX_bits rd (v1 * v_pow))
  pure RETIRE_SUCCESS

theorem jolt_sll_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sll rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  unfold jolt_sll liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  obtain ⟨s', hw⟩ := wX_shape rd (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat)) js.sail
  simp only [hw]
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sll_mul_eq_shift v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_sll_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sll rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_left v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SLL_factored rs2 rs1 rd)
    (jolt_sll_concrete rs2 rs1 rd js hwf)

end
