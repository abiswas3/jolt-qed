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

abbrev srlw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev srlw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srl_value (shift_bits_left v1 (32 : BitVec 6))
        (jolt_virtual_shift_right_bitmask_value
          (v2 ||| sign_extend (m := 64) (32 : BitVec 12)))) 31 0)

theorem execute_RTYPEW_SRLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (srlw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, srlw_sail_operation]

-- NOTE: Math theorem: the Jolt bitmask SRL sequence computes Sail SRLW.
private lemma virtual_srlw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    srlw_jolt_val v1 v2 = srlw_sail_operation v1 v2 := by
  simp only [srlw_jolt_val, srlw_sail_operation]
  rw [← srlw_shift_eq v1 v2]
  unfold jolt_virtual_srl_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value, ctz_srlw_bitmask]
  have hsign : sign_extend (m := 64) (32 : BitVec 12) = (32#64) := by decide
  have hmask :
      ((v2 ||| sign_extend (m := 64) (32 : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat + 32 := by
    rw [hsign]
    simpa only [Riscv.ori] using (or32_setWidth6_toNat v2)
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
        js'.sail = stateAfterWrite js.sail rd (srlw_sail_operation v1 v2) := by
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
  obtain ⟨js_afterSrl, h_virtual_srl_writes_shifted_result,
      h_virtual_srl_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_vreg_vreg rd
      (0 : JoltISA.VReg) (1 : JoltISA.VReg) js_afterBitmask
  have h_srl_writes_shifted_result :
      js_afterSrl.sail = stateAfterWrite js.sail rd shiftedResult := by
    change js_afterSrl.sail = stateAfterWrite js.sail rd shiftedResult
    exact h_virtual_srl_writes_shifted_result

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRLW result.
  let jolt_val := srlw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_reads_shifted_result,
      h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
      rd rd js_afterSrl js.sail shiftedResult hrd h_srl_writes_shifted_result

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.srlwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLeftShift h_left_shift_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLeftShift js_afterOri h_ori_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterOri js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSrl
      h_virtual_srl_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrl js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, v1, v2, hok1, hok2, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRLW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    rw [h_sign_extend_writes_jolt_val, h_srl_writes_shifted_result]
    change stateAfterWrite (stateAfterWrite js.sail rd shiftedResult) rd jolt_val =
      stateAfterWrite js.sail rd jolt_val
    exact stateAfterWrite_stateAfterWrite rd shiftedResult jolt_val js.sail

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's five-instruction value is Sail's SRLW value.
  have h_srlw_value :
      jolt_val = srlw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_srlw_value_eq v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srlw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRLW`. -/
theorem srlwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail := by
  obtain ⟨js_afterSignExtend, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    srlwProgram_concrete rs2 rs1 rd hrd js hwf

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SRLW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SRLW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (srlw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (srlw_sail_operation v1 v2) js.sail s' h_write).symm

end
