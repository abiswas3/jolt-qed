import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualPow2W
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLW: VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt program sequence:
1. `VirtualPow2W v0, rs2` — compute `2 ^ (rs2[4:0])`
2. `MUL rd, rs1, v0` — multiply `rs1` by the power of two
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Bridge: `sllw_mul_eq_shift` (in `Bridges/Shift.lean`).
-/

theorem execute_RTYPEW_SLLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

/-- Math bridge: the three-step Jolt SLLW value equals Sail's SLLW value. -/
private theorem sllw_value_eq_sail (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v1 * jolt_virtual_pow2w_value v2) 31 0) =
      sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  unfold jolt_virtual_pow2w_value
  rw [sllw_mul_eq_shift v1 v2]

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

/-- Program-level concrete theorem for `SLLW`.

The expansion is `VirtualPow2W` into scratch `v0`, a real-destination
multiply by that scratch value, then `VirtualSignExtendWord` on `rd`. -/
theorem sllwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `VirtualPow2W v0, rs2` writes `2 ^ rs2[4:0]` to `v0`.
  let pow2 := jolt_virtual_pow2w_value v2
  let js_afterPow2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then pow2 else js.vregs r }
  have h_pow2_succeeds :
      (JoltISA.execInstr (.VirtualPow2W (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterPow2 := by
    simpa only [js_afterPow2, pow2] using
      (JoltISA.virtual_pow2w_run_vreg_xreg
        (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `MUL rd, rs1, v0` writes the shifted word product to `rd`.
  let product := v1 * pow2
  have h_rs1_reads_v1_after_pow2 :
      rX_bits rs1 js_afterPow2.sail = .ok v1 js_afterPow2.sail := by
    simpa only [js_afterPow2] using hok1
  obtain ⟨s_afterMul, h_mul_run, h_mul_write⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_vreg rd rs1 (0 : JoltISA.VReg)
      js_afterPow2 v1 h_rs1_reads_v1_after_pow2
  have h_mul_writes_product : wX_bits rd product js.sail = .ok () s_afterMul := by
    simpa only [js_afterPow2, product, pow2] using h_mul_write
  let js_afterMul : SailJoltState := { sail := s_afterMul, vregs := js_afterPow2.vregs }
  have h_sail_after_mul :
      js_afterMul.sail = stateAfterWrite js.sail rd product := by
    simpa only [js_afterMul, product] using
      wX_bits_eq_stateAfterWrite rd product js.sail s_afterMul h_mul_writes_product
  have h_mul_succeeds :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_afterPow2 =
        .ok RETIRE_SUCCESS js_afterMul := by
    simpa only [js_afterMul] using h_mul_run

  have h_rd_reads_product : rX_bits rd s_afterMul = .ok product s_afterMul := by
    exact wX_rX_roundtrip rd product js.sail s_afterMul hrd h_mul_writes_product

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SLLW result.
  let sllwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb product 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail SLLW.
  have h_sllw_result_eq_sail :
      sllwResult =
        sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
    simpa only [sllwResult, product, pow2] using sllw_value_eq_sail v1 v2
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterMul
      product (by simpa only [js_afterMul] using h_rd_reads_product)
  have h_sign_extend_writes_result :
      wX_bits rd sllwResult s_afterMul = .ok () s_afterSignExtend := by
    simpa only [js_afterMul, sllwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js_afterPow2.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterMul.sail rd sllwResult := by
    simpa only [js', js_afterMul, sllwResult] using
      wX_bits_eq_stateAfterWrite rd sllwResult s_afterMul s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterMul =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  -- Full program succeeds by stepping through the three instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.sllwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterPow2 h_pow2_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterPow2 js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js' h_sign_extend_succeeds]
    rfl

  -- Final Sail state: the last architectural write overwrites the multiply write.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterMul.sail js'.sail
      product sllwResult
      (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      h_sail_after_mul h_sail_after_sign_extend h_sllw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SLLW_factored rs2 rs1 rd)
    (sllwProgram_concrete rs2 rs1 rd hrd js hwf)

end
