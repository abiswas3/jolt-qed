import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.ORI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.SLLI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLW: SLLI + ORI + bitmask + VirtualSRL + VSEW = Sail SRLW

Jolt program sequence:
1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `ORI v1, rs2, 32` — set bit 5 of the shift amount
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask
4. `VirtualSRL rd, v0, v1` — logical right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

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

-- NOTE: Math theorem: the Jolt bitmask SRL sequence computes Sail SRLW.
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
    simpa only [Riscv.ori] using or32_setWidth6_toNat v2
  rw [hmask]
  simp only [shift_bits_left]
  rfl

/-- State plumbing for two writes to the same architectural register. If the
first instruction writes `first`, the second writes `second`, and `second` is
the desired `final` value, then the net Sail state is just the final write. -/
private theorem sail_state_after_two_writes_eq_final
    (rd : regidx)
    (s0 s1 s2 : SailState)
    (first second final : BitVec 64)
    (h_sail_after_first : s1 = stateAfterWrite s0 rd first)
    (h_sail_after_second : s2 = stateAfterWrite s1 rd second)
    (h_second_eq_final : second = final) :
    s2 = stateAfterWrite s0 rd final := by
  calc
    s2 = stateAfterWrite s1 rd second := h_sail_after_second
    _ = stateAfterWrite (stateAfterWrite s0 rd first) rd second := by
          rw [h_sail_after_first]
    _ = stateAfterWrite s0 rd second := by
          exact stateAfterWrite_stateAfterWrite rd first second s0
    _ = stateAfterWrite s0 rd final := by
          rw [h_second_eq_final]

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

  -- Instruction 1: `SLLI v0, rs1, 32` writes the left-shifted source to `v0`.
  let leftShiftedSource := shift_bits_left v1 (32 : BitVec 6)
  let js_afterLeftShift : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then leftShiftedSource else js.vregs r }
  have h_left_shift_succeeds :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.xreg rs1) (32 : BitVec 6))).run js =
        .ok RETIRE_SUCCESS js_afterLeftShift := by
    simpa only [js_afterLeftShift, leftShiftedSource] using
      (JoltISA.slli_run_vreg_xreg (0 : JoltISA.VReg) rs1
        (32 : BitVec 6) js v1 hok1)

  -- Instruction 2: `ORI v1, rs2, 32` writes the encoded shift amount to `v1`.
  let encodedShift := v2 ||| sign_extend (m := 64) (32 : BitVec 12)
  let js_afterOri : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then encodedShift
        else js_afterLeftShift.vregs r }
  have h_ori_succeeds :
      (JoltISA.execInstr (.ORI (.vreg 1) (.xreg rs2) (32 : BitVec 12))).run
        js_afterLeftShift =
        .ok RETIRE_SUCCESS js_afterOri := by
    have h_rs2_reads_v2_after_left_shift :
        rX_bits rs2 js_afterLeftShift.sail = .ok v2 js_afterLeftShift.sail := by
      simpa only [js_afterLeftShift] using hok2
    simpa only [js_afterOri, js_afterLeftShift, encodedShift] using
      (JoltISA.ori_run_vreg_xreg (1 : JoltISA.VReg) rs2
        (32 : BitVec 12) js_afterLeftShift v2 h_rs2_reads_v2_after_left_shift)

  -- Instruction 3: `VirtualShiftRightBitmask v1, v1` writes the shift bitmask to `v1`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value encodedShift
  let js_afterBitmask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then shiftBitmask
        else js_afterOri.vregs r }
  have h_bitmask_succeeds :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1))).run
        js_afterOri =
        .ok RETIRE_SUCCESS js_afterBitmask := by
    simpa only [js_afterBitmask, js_afterOri, shiftBitmask, encodedShift, if_pos rfl] using
      (JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
        (1 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterOri)

  -- Instruction 4: `VirtualSRL rd, v0, v1` writes the shifted result to `rd`.
  let shiftedResult := jolt_virtual_srl_value leftShiftedSource shiftBitmask
  obtain ⟨s_afterSrl, h_virtual_srl_run, h_virtual_srl_write⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_vreg_vreg rd
      (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterBitmask
  have h_srl_writes_shifted_result :
      wX_bits rd shiftedResult js.sail = .ok () s_afterSrl := by
    simpa (config := { decide := true }) only
      [js_afterBitmask, js_afterOri, js_afterLeftShift, shiftedResult,
        leftShiftedSource, shiftBitmask, encodedShift] using
      h_virtual_srl_write
  let js_afterSrl : SailJoltState := { sail := s_afterSrl, vregs := js_afterBitmask.vregs }
  have h_sail_after_srl :
      js_afterSrl.sail = stateAfterWrite js.sail rd shiftedResult := by
    simpa only [js_afterSrl, shiftedResult] using
      wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterSrl
        h_srl_writes_shifted_result
  have h_virtual_srl_succeeds :
      (JoltISA.execInstr (.VirtualSRL (.xreg rd) (.vreg 0) (.vreg 1))).run
        js_afterBitmask =
        .ok RETIRE_SUCCESS js_afterSrl := by
    simpa only [js_afterSrl] using h_virtual_srl_run

  have h_rd_reads_shifted_result :
      rX_bits rd s_afterSrl = .ok shiftedResult s_afterSrl := by
    exact wX_rX_roundtrip rd shiftedResult js.sail s_afterSrl hrd
      h_srl_writes_shifted_result

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRLW result.
  let srlwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb shiftedResult 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail SRLW.
  have h_srlw_result_eq_sail :
      srlwResult =
        sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
    simpa only [srlwResult, shiftedResult, leftShiftedSource, shiftBitmask, encodedShift] using
      virtual_srlw_value_eq v1 v2
  obtain ⟨s_afterResultSignExtend, h_result_sign_extend_run, h_result_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterSrl
      shiftedResult (by simpa only [js_afterSrl] using h_rd_reads_shifted_result)
  have h_result_sign_extend_writes_result :
      wX_bits rd srlwResult s_afterSrl = .ok () s_afterResultSignExtend := by
    simpa only [js_afterSrl, srlwResult] using h_result_sign_extend_write

  let js' : SailJoltState := { sail := s_afterResultSignExtend, vregs := js_afterBitmask.vregs }
  have h_sail_after_result_sign_extend :
      js'.sail = stateAfterWrite js_afterSrl.sail rd srlwResult := by
    simpa only [js', js_afterSrl, srlwResult] using
      wX_bits_eq_stateAfterWrite rd srlwResult s_afterSrl s_afterResultSignExtend
        h_result_sign_extend_writes_result
  have h_result_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterSrl =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_result_sign_extend_run

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.srlwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLeftShift h_left_shift_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLeftShift js_afterOri h_ori_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterOri js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSrl
      h_virtual_srl_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrl js'
      h_result_sign_extend_succeeds]
    rfl

  -- Final Sail state: the last architectural write overwrites the shift write.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterSrl.sail js'.sail
      shiftedResult srlwResult
      (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      h_sail_after_srl h_sail_after_result_sign_extend h_srlw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

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
