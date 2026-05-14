import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

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

theorem execute_RTYPEW_SRAW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith
        (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

private lemma virtual_sraw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (jolt_virtual_sra_value
          (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
          (jolt_virtual_shift_right_bitmask_value
            (v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  have hsign : sign_extend (m := 64) (0x1f : BitVec 12) = (0x1f#64) := by decide
  have hmask :
      ((v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat := by
    rw [hsign]
    simpa [Riscv.andi] using and31_setWidth6_toNat v2
  rw [hmask]
  exact sraw_virtual_sra_value v1 v2

/-- Program-level concrete theorem for `SRAW`.

This follows the five emitted steps: sign-extend `rs1[31:0]` into scratch
`v0`, mask `rs2` into scratch `v1`, encode `v1` as a right-shift bitmask, run
`VirtualSRA`, then sign-extend `rd` once more. -/
theorem srawProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  let sx := sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)
  let maskIn := v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)
  let bitmask := jolt_virtual_shift_right_bitmask_value maskIn
  let raw := jolt_virtual_sra_value sx bitmask
  let js_sx : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then sx else js.vregs r }
  have hsext_v :
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg 0) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js_sx := by
    simpa [js_sx, sx] using
      (JoltISA.execInstr_sextw_xreg_vreg_run (0 : JoltISA.VReg) rs1 js v1 hok1)
  let js_andi : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then maskIn else js_sx.vregs r }
  have handi :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.xreg rs2) (0x1f : BitVec 12))).run js_sx =
        .ok RETIRE_SUCCESS js_andi := by
    have hread : rX_bits rs2 js_sx.sail = .ok v2 js_sx.sail := by
      simpa [js_sx] using hok2
    simpa [js_andi, maskIn] using
      (JoltISA.execInstr_andi_xreg_vreg_run (1 : JoltISA.VReg) rs2
        (0x1f : BitVec 12) js_sx v2 hread)
  let js_mask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then bitmask else js_andi.vregs r }
  have hmask :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1))).run js_andi =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, js_andi, bitmask, maskIn] using
      (JoltISA.execInstr_virtualShiftRightBitmask_vreg_vreg_run
        (1 : JoltISA.VReg) (1 : JoltISA.VReg) js_andi)
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_mask.vregs }
  have hsra :
      (JoltISA.execInstr (.VirtualSRA (.xreg rd) (.vreg 0) (.vreg 1))).run js_mask =
        .ok RETIRE_SUCCESS js_raw := by
    have hwrite :
        wX_bits rd
          (jolt_virtual_sra_value (js_mask.vregs (0 : JoltISA.VReg))
            (js_mask.vregs (1 : JoltISA.VReg))) js_mask.sail = .ok () s_raw := by
      simpa (config := { decide := true }) [js_mask, js_andi, js_sx, raw, sx, bitmask] using
        hw_raw
    simpa [js_raw] using
      (JoltISA.execInstr_virtualSRA_vreg_vreg_xreg_run rd
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
  · unfold JoltISA.srawProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_sx hsext_v]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_sx js_andi handi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_andi js_mask hmask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_raw hsra]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw, sx, bitmask, maskIn]
    congr 1
    simpa using virtual_sraw_value_eq v1 v2

/-- Main program-level equivalence for `SRAW`. -/
theorem srawProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SRAW_factored rs2 rs1 rd)
    (srawProgram_concrete rs2 rs1 rd hrd js hwf)

end
