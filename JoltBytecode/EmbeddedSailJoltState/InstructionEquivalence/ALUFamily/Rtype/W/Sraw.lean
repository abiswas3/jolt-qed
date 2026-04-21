import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAW: 5-step bitmask-encoded arithmetic right shift = Sail SRAW

Jolt decomposes SRAW into (from `BytecodeExpansions/Sraw.lean`):

1. `VirtualSignExtendWord rs1 → v0` — sign-extend `rs1[31:0]` to 64 bits
2. `ANDI rs2, 0x1f → v1` — mask shift amount to 5 bits
3. `VirtualShiftRightBitmask` — compute bitmask from v1
4. `VirtualSRA v0, bitmask → rd` — arithmetic right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd → rd`

Bridge: `sraw_five_step_value` (in `Bridges/Shift.lean`).
-/

theorem execute_RTYPEW_SRAW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith
        (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind, bind_assoc]

def jolt_sraw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- VirtualSignExtendWord rs1 → v0
  let v1 ← liftSail (rX_bits rs1)
  writeVReg 0 (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
  -- ANDI rs2, 0x1f → v1
  let v2 ← liftSail (rX_bits rs2)
  writeVReg 1 (v2 &&& 0x1f#64)
  -- VirtualSRA via bitmask → rd
  let v_rs1 ← readVReg 0
  let v_shamt ← readVReg 1
  liftSail (wX_bits rd (v_rs1 >>> ctz (sraw_bitmask v_shamt)))
  -- VirtualSignExtendWord rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_sraw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sraw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_sraw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get, MonadStateOf.get, EStateM.get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true, ite_false]
  obtain ⟨s3, hw1⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>> ctz (sraw_bitmask (v2 &&& 0x1f#64))) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>> ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sraw_five_step_value v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

theorem jolt_sraw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sraw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SRAW_factored rs2 rs1 rd)
    (jolt_sraw_concrete rs2 rs1 rd hrd js hwf)

end
