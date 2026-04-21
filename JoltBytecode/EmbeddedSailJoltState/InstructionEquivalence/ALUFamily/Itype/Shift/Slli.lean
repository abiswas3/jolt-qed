import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Shift.Family

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLI: Jolt VirtualMULI = Sail SLLI

Jolt decomposes SLLI as `VirtualMULI rd, rs1, 2^shamt`. Multiply by
`2^s` = left shift by `s`; bridge is inlined.
-/

private theorem extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp [BitVec.getLsbD_extractLsb]; rfl

private theorem mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem slli_mul_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ shamt.toNat) =
    shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [extractLsb_shamt6_id]
  exact mul_pow2_eq_shiftLeft v shamt

theorem execute_SHIFTIOP_SLLI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

def jolt_slli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v * BitVec.ofNat 64 (2 ^ shamt.toNat)))
  pure RETIRE_SUCCESS

theorem jolt_slli_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_slli shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  unfold jolt_slli liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v, hok⟩ := hwf rs1
  simp only [hok]
  obtain ⟨s', hw⟩ := wX_shape rd (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) js.sail
  simp only [hw]
  refine ⟨_, v, rfl, rfl, ?_⟩
  rw [← slli_mul_eq_shift v shamt]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_slli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_slli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => shift_bits_left v
      (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_SHIFTIOP_SLLI_factored shamt rs1 rd)
    (jolt_slli_concrete shamt rs1 rd js hwf)

end
