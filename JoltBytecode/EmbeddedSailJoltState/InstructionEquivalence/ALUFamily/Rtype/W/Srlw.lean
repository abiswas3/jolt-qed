import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

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

theorem execute_RTYPEW_SRLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

private lemma virtual_srlw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (jolt_virtual_srl_value (shift_bits_left v1 (32 : BitVec 6))
          (jolt_virtual_shift_right_bitmask_value
            (v2 ||| sign_extend (m := 64) (32 : BitVec 12)))) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [← srlw_shift_eq v1 v2]
  unfold jolt_virtual_srl_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value, ctz_srlw_bitmask]
  have hsign : sign_extend (m := 64) (32 : BitVec 12) = (32#64) := by decide
  have hmask :
      ((v2 ||| sign_extend (m := 64) (32 : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat + 32 := by
    rw [hsign]
    simpa [Riscv.ori] using or32_setWidth6_toNat v2
  rw [hmask]
  simp only [shift_bits_left]
  rfl

/-- Program-level concrete theorem for `SRLW`.

The program theorem follows the five Rust-emitted steps: shift `rs1` left into
scratch `v0`, set bit five of `rs2` in scratch `v1`, encode that as a virtual
right-shift bitmask, run `VirtualSRL`, and finally sign-extend `rd`. -/
theorem srlwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  let shifted := shift_bits_left v1 (32 : BitVec 6)
  let maskIn := v2 ||| sign_extend (m := 64) (32 : BitVec 12)
  let bitmask := jolt_virtual_shift_right_bitmask_value maskIn
  let raw := jolt_virtual_srl_value shifted bitmask
  let js_shift : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then shifted else js.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.xreg rs1) (32 : BitVec 6))).run js =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift, shifted] using
      (JoltISA.execInstr_slli_xreg_vreg_run (0 : JoltISA.VReg) rs1
        (32 : BitVec 6) js v1 hok1)
  let js_ori : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then maskIn else js_shift.vregs r }
  have hori :
      (JoltISA.execInstr (.ORI (.vreg 1) (.xreg rs2) (32 : BitVec 12))).run js_shift =
        .ok RETIRE_SUCCESS js_ori := by
    have hread : rX_bits rs2 js_shift.sail = .ok v2 js_shift.sail := by
      simpa [js_shift] using hok2
    simpa [js_ori, maskIn] using
      (JoltISA.execInstr_ori_xreg_vreg_run (1 : JoltISA.VReg) rs2
        (32 : BitVec 12) js_shift v2 hread)
  let js_mask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then bitmask else js_ori.vregs r }
  have hmask :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1))).run js_ori =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, js_ori, bitmask, maskIn] using
      (JoltISA.execInstr_virtualShiftRightBitmask_vreg_vreg_run
        (1 : JoltISA.VReg) (1 : JoltISA.VReg) js_ori)
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_mask.vregs }
  have hsrl :
      (JoltISA.execInstr (.VirtualSRL (.xreg rd) (.vreg 0) (.vreg 1))).run js_mask =
        .ok RETIRE_SUCCESS js_raw := by
    have hwrite :
        wX_bits rd
          (jolt_virtual_srl_value (js_mask.vregs (0 : JoltISA.VReg))
            (js_mask.vregs (1 : JoltISA.VReg))) js_mask.sail = .ok () s_raw := by
      simpa (config := { decide := true }) [js_mask, js_ori, js_shift, raw, shifted, bitmask] using
        hw_raw
    simpa [js_raw] using
      (JoltISA.execInstr_virtualSRL_vreg_vreg_xreg_run rd
        (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_mask s_raw hwrite)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js_mask.vregs }
  have hsextw :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.srlwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_shift hslli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_ori hori]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_ori js_mask hmask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_raw hsrl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw, shifted, bitmask, maskIn]
    congr 1
    simpa using virtual_srlw_value_eq v1 v2

/-- Main program-level equivalence for `SRLW`. -/
theorem srlwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SRLW_factored rs2 rs1 rd)
    (srlwProgram_concrete rs2 rs1 rd hrd js hwf)

end
