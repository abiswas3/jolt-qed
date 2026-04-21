import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Family
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRA: Jolt VirtualSRA via bitmask = Sail SRA

Same bitmask encoding as SRL but with arithmetic (sign-extending) right
shift.
-/

def sra_bitmask (rs2_val : BitVec 64) : Nat :=
  let shift := (rs2_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_sra_bitmask (rs2_val : BitVec 64) :
    ctz (sra_bitmask rs2_val) = (rs2_val.setWidth 6).toNat := by
  unfold sra_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (rs2_val.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (rs2_val.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private lemma sra_bitmask_eq_shift (v1 v2 : BitVec 64) :
    v1.sshiftRight (ctz (sra_bitmask v2)) =
    shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_right_arith LeanRV64D.Functions.log2_xlen
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_sra_bitmask]
  congr 1

theorem execute_RTYPE_SRA_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

def jolt_sra (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1.sshiftRight (ctz (sra_bitmask v2))))
  pure RETIRE_SUCCESS

theorem jolt_sra_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sra rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  unfold jolt_sra liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  obtain ⟨s', hw⟩ := wX_shape rd (v1.sshiftRight (ctz (sra_bitmask v2))) js.sail
  simp only [hw]
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sra_bitmask_eq_shift v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_sra_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sra rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SRA_factored rs2 rs1 rd)
    (jolt_sra_concrete rs2 rs1 rd js hwf)

end
