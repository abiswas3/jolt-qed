import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Srl

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SRL: Jolt VirtualSRL via bitmask = Sail SRL

Jolt decomposes SRL as (from BytecodeExpansions/Srl.lean):
1. VirtualShiftRightBitmask rs2 → bitmask
2. VirtualSRL rd, rs1, bitmask  — logical right shift by ctz(bitmask)

ctz(bitmask) = rs2[5:0], so this equals Sail's SRL.
-/

-- Bridge: Jolt's logical shift via ctz(bitmask) = Sail's shift_bits_right.
private lemma srl_bitmask_eq_shift (v1 v2 : BitVec 64) :
    v1 >>> ctz (srl_bitmask v2) =
    shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_right LeanRV64D.Functions.log2_xlen
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_srl_bitmask]
  congr 1

-- Jolt's SRL: read rs1, logical right shift by ctz(bitmask of rs2), write to rd.
def jolt_srl (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1 >>> ctz (srl_bitmask v2)))
  pure RETIRE_SUCCESS

-- Factoring: execute_RTYPE SRL reads rs1, rs2, right-shifts v1 by v2[5:0].
private theorem execute_RTYPE_SRL_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

-- Concrete: characterise what jolt_srl writes to rd.
theorem jolt_srl_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_srl rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (v1 >>> ctz (srl_bitmask v2)) := by
  unfold jolt_srl liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  obtain ⟨s', hw⟩ := wX_shape rd (v1 >>> ctz (srl_bitmask v2)) js.sail
  simp only [hw]
  exact ⟨_, v1, v2, rfl, rfl, rfl, wX_bits_eq_stateAfterWrite rd _ js.sail s' hw⟩

-- Running Jolt's SRL and projecting equals running Sail's SRL.
theorem jolt_srl_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srl rs2 rs1 rd).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRL).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_srl_concrete rs2 rs1 rd js hwf
  rw [execute_RTYPE_SRL_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_srl rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail, srl_bitmask_eq_shift v1 v2]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
