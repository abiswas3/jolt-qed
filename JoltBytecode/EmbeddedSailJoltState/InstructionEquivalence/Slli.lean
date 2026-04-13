import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Slli

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SLLI: Jolt VirtualMULI = Sail SLLI

Jolt decomposes SLLI as:
1. VirtualMULI rd, rs1, 2^(shamt[5:0]) — multiply rs1 by 2^shift (= left shift)
-/

-- Bridge: multiply by 2^shamt = shift_bits_left, accounting for extractLsb
-- extractLsb shamt 5 0 = shamt for BitVec 6
private lemma extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp [BitVec.getLsbD_extractLsb]; rfl

-- multiply by 2^n = shift left by n
private lemma mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private lemma slli_mul_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ shamt.toNat) =
    shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [extractLsb_shamt6_id]
  exact mul_pow2_eq_shiftLeft v shamt

-- Jolt's SLLI: read rs1, multiply by 2^shamt, write to rd.
def jolt_slli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v * BitVec.ofNat 64 (2 ^ shamt.toNat)))
  pure RETIRE_SUCCESS

-- Factoring: execute_SHIFTIOP SLLI reads rs1, left-shifts by shamt.
private theorem execute_SHIFTIOP_SLLI_eq_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

-- Concrete: characterise what jolt_slli writes to rd.
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

-- Running Jolt's SLLI and projecting equals running Sail's SLLI.
theorem jolt_slli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_slli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_slli_concrete shamt rs1 rd js hwf
  rw [execute_SHIFTIOP_SLLI_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  show projectResult ((jolt_slli shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
