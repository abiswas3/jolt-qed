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
    simpa only [Riscv.andi] using and31_setWidth6_toNat v2
  rw [hmask]
  exact sraw_virtual_sra_value v1 v2

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

  -- Instruction 1: `VirtualSignExtendWord v0, rs1` writes the signed source word to `v0`.
  let signedSource := sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)
  let js_afterSourceSignExtend : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then signedSource else js.vregs r }
  have h_source_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg 0) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js_afterSourceSignExtend := by
    simpa only [js_afterSourceSignExtend, signedSource] using
      (JoltISA.virtual_sign_extend_word_run_vreg_xreg (0 : JoltISA.VReg) rs1 js v1 hok1)

  -- Instruction 2: `ANDI v1, rs2, 0x1f` writes the masked shift amount to `v1`.
  let maskedShift := v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)
  let js_afterAndi : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then maskedShift
        else js_afterSourceSignExtend.vregs r }
  have h_andi_succeeds :
      (JoltISA.execInstr (.ANDI (.vreg 1) (.xreg rs2) (0x1f : BitVec 12))).run
        js_afterSourceSignExtend =
        .ok RETIRE_SUCCESS js_afterAndi := by
    have h_rs2_reads_v2_after_source_sign_extend :
        rX_bits rs2 js_afterSourceSignExtend.sail =
          .ok v2 js_afterSourceSignExtend.sail := by
      simpa only [js_afterSourceSignExtend] using hok2
    simpa only [js_afterAndi, js_afterSourceSignExtend, maskedShift] using
      (JoltISA.andi_run_vreg_xreg (1 : JoltISA.VReg) rs2
        (0x1f : BitVec 12) js_afterSourceSignExtend v2
        h_rs2_reads_v2_after_source_sign_extend)

  -- Instruction 3: `VirtualShiftRightBitmask v1, v1` writes the shift bitmask to `v1`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value maskedShift
  let js_afterBitmask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then shiftBitmask
        else js_afterAndi.vregs r }
  have h_bitmask_succeeds :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1))).run
        js_afterAndi =
        .ok RETIRE_SUCCESS js_afterBitmask := by
    simpa only [js_afterBitmask, js_afterAndi, shiftBitmask, maskedShift, if_pos rfl] using
      (JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
        (1 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterAndi)

  -- Instruction 4: `VirtualSRA rd, v0, v1` writes the shifted result to `rd`.
  let shiftedResult := jolt_virtual_sra_value signedSource shiftBitmask
  obtain ⟨s_afterSra, h_virtual_sra_run, h_virtual_sra_write⟩ :=
    JoltISA.exists_state_after_virtual_sra_run_xreg_vreg_vreg rd
      (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterBitmask
  have h_sra_writes_shifted_result :
      wX_bits rd shiftedResult js.sail = .ok () s_afterSra := by
    simpa (config := { decide := true }) only
      [js_afterBitmask, js_afterAndi, js_afterSourceSignExtend, shiftedResult,
        signedSource, shiftBitmask, maskedShift] using
      h_virtual_sra_write
  let js_afterSra : SailJoltState := { sail := s_afterSra, vregs := js_afterBitmask.vregs }
  have h_sail_after_sra :
      js_afterSra.sail = stateAfterWrite js.sail rd shiftedResult := by
    simpa only [js_afterSra, shiftedResult] using
      wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterSra
        h_sra_writes_shifted_result
  have h_virtual_sra_succeeds :
      (JoltISA.execInstr (.VirtualSRA (.xreg rd) (.vreg 0) (.vreg 1))).run
        js_afterBitmask =
        .ok RETIRE_SUCCESS js_afterSra := by
    simpa only [js_afterSra] using h_virtual_sra_run

  have h_rd_reads_shifted_result :
      rX_bits rd s_afterSra = .ok shiftedResult s_afterSra := by
    exact wX_rX_roundtrip rd shiftedResult js.sail s_afterSra hrd
      h_sra_writes_shifted_result

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRAW result.
  let srawResult := sign_extend (m := 64) (Sail.BitVec.extractLsb shiftedResult 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail SRAW.
  have h_sraw_result_eq_sail :
      srawResult =
        sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
    simpa only [srawResult, shiftedResult, signedSource, shiftBitmask, maskedShift] using
      virtual_sraw_value_eq v1 v2
  obtain ⟨s_afterResultSignExtend, h_result_sign_extend_run, h_result_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterSra
      shiftedResult (by simpa only [js_afterSra] using h_rd_reads_shifted_result)
  have h_result_sign_extend_writes_result :
      wX_bits rd srawResult s_afterSra = .ok () s_afterResultSignExtend := by
    simpa only [js_afterSra, srawResult] using h_result_sign_extend_write

  let js' : SailJoltState := { sail := s_afterResultSignExtend, vregs := js_afterBitmask.vregs }
  have h_sail_after_result_sign_extend :
      js'.sail = stateAfterWrite js_afterSra.sail rd srawResult := by
    simpa only [js', js_afterSra, srawResult] using
      wX_bits_eq_stateAfterWrite rd srawResult s_afterSra s_afterResultSignExtend
        h_result_sign_extend_writes_result
  have h_result_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterSra =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_result_sign_extend_run

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.srawProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSourceSignExtend
      h_source_sign_extend_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSourceSignExtend js_afterAndi
      h_andi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAndi js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSra
      h_virtual_sra_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSra js'
      h_result_sign_extend_succeeds]
    rfl

  -- Final Sail state: the last architectural write overwrites the shift write.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterSra.sail js'.sail
      shiftedResult srawResult
      (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      h_sail_after_sra h_sail_after_result_sign_extend h_sraw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

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
