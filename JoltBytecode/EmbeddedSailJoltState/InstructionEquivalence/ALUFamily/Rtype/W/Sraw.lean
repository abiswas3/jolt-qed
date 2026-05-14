import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.ANDI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRA
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAW: 5-step bitmask-encoded arithmetic right shift = Sail SRAW

Jolt program sequence:
1. `VirtualSignExtendWord v0, rs1` — sign-extend `rs1[31:0]` to 64 bits
2. `ANDI v1, rs2, 0x1f` — mask shift amount to 5 bits
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask from `v1`
4. `VirtualSRA rd, v0, v1` — arithmetic right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

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

-- NOTE: Math theorem: the Jolt bitmask SRA sequence computes Sail SRAW.
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

  -- Instruction 1: `VirtualSignExtendWord v0, rs1` writes `sx = sext(v1[31:0])` to `v0`.
  let js_sx : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then sx else js.vregs r }
  have instr1_VirtualSignExtendWord_writes_sx :
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg 0) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js_sx := by
    simpa [js_sx, sx] using
      (JoltISA.execInstr_sextw_xreg_vreg_run (0 : JoltISA.VReg) rs1 js v1 hok1)

  -- Instruction 2: `ANDI v1, rs2, 0x1f` writes `maskIn` to `v1`.
  let js_andi : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then maskIn else js_sx.vregs r }
  have instr2_ANDI_writes_maskIn :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.xreg rs2) (0x1f : BitVec 12))).run js_sx =
        .ok RETIRE_SUCCESS js_andi := by
    have hread : rX_bits rs2 js_sx.sail = .ok v2 js_sx.sail := by
      simpa [js_sx] using hok2
    simpa [js_andi, maskIn] using
      (JoltISA.execInstr_andi_xreg_vreg_run (1 : JoltISA.VReg) rs2
        (0x1f : BitVec 12) js_sx v2 hread)

  -- Instruction 3: `VirtualShiftRightBitmask v1, v1` writes `bitmask` to `v1`.
  let js_mask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then bitmask else js_andi.vregs r }
  have instr3_VirtualShiftRightBitmask_writes_bitmask :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1))).run js_andi =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, js_andi, bitmask, maskIn] using
      (JoltISA.execInstr_virtualShiftRightBitmask_vreg_vreg_run
        (1 : JoltISA.VReg) (1 : JoltISA.VReg) js_andi)

  -- Instruction 4: `VirtualSRA rd, v0, v1` writes `raw` to `rd`.
  obtain ⟨s_raw, hrun_VirtualSRA, hw_raw_sra⟩ :=
    JoltISA.execInstr_virtualSRA_vreg_vreg_xreg_run_of_vregs rd
      (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_mask
  have hw_raw : wX_bits rd raw js.sail = .ok () s_raw := by
    simpa (config := { decide := true }) [js_mask, js_andi, js_sx, raw, sx, bitmask] using
      hw_raw_sra
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_mask.vregs }
  have instr4_VirtualSRA_writes_raw :
      (JoltISA.execInstr (.VirtualSRA (.xreg rd) (.vreg 0) (.vreg 1))).run js_mask =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_VirtualSRA

  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hrun_VirtualSignExtendWord, hw_final_raw⟩ :=
    JoltISA.execInstr_sextw_xreg_xreg_run_of_read rd rd js_raw raw
      (by simpa [js_raw] using hread_rd)
  have hw_final : wX_bits rd final s_raw = .ok () s_final := by
    simpa [js_raw, final] using hw_final_raw

  let js' : SailJoltState := { sail := s_final, vregs := js_mask.vregs }
  have instr5_VirtualSignExtendWord_writes_final :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSignExtendWord
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.srawProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_sx
      instr1_VirtualSignExtendWord_writes_sx]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_sx js_andi instr2_ANDI_writes_maskIn]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_andi js_mask
      instr3_VirtualShiftRightBitmask_writes_bitmask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js_raw instr4_VirtualSRA_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr5_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `virtual_sraw_value_eq` matches the virtual sequence with Sail SRAW.
    have math_raw_low32 :
        final =
          sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
            (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
      dsimp [final, raw, sx, bitmask, maskIn]
      simpa using virtual_sraw_value_eq v1 v2
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
            (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

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
