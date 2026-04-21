import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Shift.Family
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAI: Jolt VirtualSRAI via bitmask = Sail SRAI

Jolt precomputes a bitmask from the shift amount and invokes
`VirtualSRAI`, which performs arithmetic right shift by `ctz(bitmask)`.
No VSEW step.
-/

def srai_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_srai_bitmask (shamt : BitVec 64) :
    ctz (srai_bitmask shamt) = (shamt.setWidth 6).toNat := by
  unfold srai_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (shamt.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private lemma srai_bitmask_eq_arith_shift (v : BitVec 64) (shamt : BitVec 6) :
    v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64))) =
    shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0) := by
  unfold shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_srai_bitmask]
  congr 1; omega

theorem execute_SHIFTIOP_SRAI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRAI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, LeanRV64D.Functions.log2_xlen]

def jolt_srai (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64)))))
  pure RETIRE_SUCCESS

theorem jolt_srai_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_srai shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0)) := by
  unfold jolt_srai liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v, hok⟩ := hwf rs1
  simp only [hok]
  obtain ⟨s', hw⟩ := wX_shape rd (v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64)))) js.sail
  simp only [hw]
  refine ⟨_, v, rfl, rfl, ?_⟩
  rw [← srai_bitmask_eq_arith_shift v shamt]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_srai_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srai shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRAI).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))
    (execute_SHIFTIOP_SRAI_factored shamt rs1 rd)
    (jolt_srai_concrete shamt rs1 rd js hwf)

end
