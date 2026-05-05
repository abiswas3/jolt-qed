import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLW: VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt decomposes SLLW into (from `BytecodeExpansions/Sllw.lean`):

1. `VirtualPow2W v_pow, rs2` — compute `2 ^ (rs2[4:0])` into v0
2. `MUL rd, rs1, v_pow` — multiply rs1 by the power of two
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits

Bridge: `sllw_mul_eq_shift` (in `Bridges/Shift.lean`).
-/

theorem execute_RTYPEW_SLLW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

def jolt_sllw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- VirtualPow2W: compute 2^(rs2[4:0]) into v0
  let v2 ← liftSail (rX_bits rs2)
  let v_pow := BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)
  writeVReg 0 v_pow
  -- MUL rd, rs1, v0
  let v1 ← liftSail (rX_bits rs1)
  let v_pow ← readVReg 0
  liftSail (wX_bits rd (v1 * v_pow))
  -- VirtualSignExtendWord rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_sllw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sllw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_sllw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true]
  obtain ⟨s3, hw1⟩ := wX_shape rd (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sllw_mul_eq_shift v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

theorem jolt_sllw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sllw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SLLW_factored rs2 rs1 rd)
    (jolt_sllw_concrete rs2 rs1 rd hrd js hwf)

end
