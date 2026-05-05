import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLW: SLLI + ORI + bitmask + VirtualSRL + VSEW = Sail SRLW

Jolt decomposes SRLW into (from `BytecodeExpansions/Srlw.lean`):

1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `ORI v1, rs2, 32` — set bit 5 of shift amount
3. `VirtualShiftRightBitmask` — compute bitmask
4. `VirtualSRL rd, v0, v1` — logical right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd`

Bridge: `srlw_shift_eq` (in `Bridges/Shift.lean`).
-/

theorem execute_RTYPEW_SRLW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

def jolt_srlw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  writeVReg 0 (v1 <<< 32)
  let v2 ← liftSail (rX_bits rs2)
  let v_bitmask := srlw_bitmask v2
  let v_rs1 ← readVReg 0
  liftSail (wX_bits rd (v_rs1 >>> ctz v_bitmask))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_srlw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_srlw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_srlw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true]
  obtain ⟨s3, hw1⟩ := wX_shape rd ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← srlw_shift_eq v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

theorem jolt_srlw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srlw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SRLW_factored rs2 rs1 rd)
    (jolt_srlw_concrete rs2 rs1 rd hrd js hwf)

end
