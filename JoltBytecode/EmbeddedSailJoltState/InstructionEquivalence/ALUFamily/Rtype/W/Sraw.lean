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

abbrev sraw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sraw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_sra_value
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
        (jolt_virtual_shift_right_bitmask_value
          (v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)))) 31 0)

theorem execute_RTYPEW_SRAW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sraw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, sraw_sail_operation]

-- NOTE: Math theorem: the Jolt bitmask SRA sequence computes Sail SRAW.
private lemma virtual_sraw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    sraw_jolt_val v1 v2 = sraw_sail_operation v1 v2 := by
  simp only [sraw_jolt_val, sraw_sail_operation]
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  have hsign : sign_extend (m := 64) (0x1f : BitVec 12) = (0x1f#64) := by decide
  have hmask :
      ((v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat := by
    rw [hsign]
    simpa only [Riscv.andi] using (and31_setWidth6_toNat v2)
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
        js'.sail = stateAfterWrite js.sail rd (sraw_sail_operation v1 v2) := by
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
  obtain ⟨js_afterSra, h_virtual_sra_writes_shifted_result,
      h_virtual_sra_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sra_run_xreg_vreg_vreg rd
      (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterBitmask
  have h_sra_writes_shifted_result :
      js_afterSra.sail = stateAfterWrite js.sail rd shiftedResult := by
    change js_afterSra.sail = stateAfterWrite js.sail rd shiftedResult
    exact h_virtual_sra_writes_shifted_result

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRAW result.
  let jolt_val := sraw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_reads_shifted_result,
      h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
      rd rd js_afterSra js.sail shiftedResult hrd h_sra_writes_shifted_result

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.srawProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSourceSignExtend
      h_source_sign_extend_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSourceSignExtend js_afterAndi
      h_andi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAndi js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSra
      h_virtual_sra_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSra js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, v1, v2, hok1, hok2, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRAW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    rw [h_sign_extend_writes_jolt_val, h_sra_writes_shifted_result]
    change stateAfterWrite (stateAfterWrite js.sail rd shiftedResult) rd jolt_val =
      stateAfterWrite js.sail rd jolt_val
    exact stateAfterWrite_stateAfterWrite rd shiftedResult jolt_val js.sail

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's five-instruction value is Sail's SRAW value.
  have h_sraw_value :
      jolt_val = sraw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_sraw_value_eq v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sraw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRAW`. -/
theorem srawProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail := by
  obtain ⟨js_afterSignExtend, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    srawProgram_concrete rs2 rs1 rd hrd js hwf

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SRAW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SRAW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (sraw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sraw_sail_operation v1 v2) js.sail s' h_write).symm

end
