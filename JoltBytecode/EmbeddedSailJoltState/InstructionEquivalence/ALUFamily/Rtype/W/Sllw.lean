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

abbrev sllw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sllw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v1 * jolt_virtual_pow2w_value v2) 31 0)

theorem execute_RTYPEW_SLLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sllw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, sllw_sail_operation]

/-- Math bridge: the three-step Jolt SLLW value equals Sail's SLLW value. -/
private theorem sllw_value_eq_sail (v1 v2 : BitVec 64) :
    sllw_jolt_val v1 v2 = sllw_sail_operation v1 v2 := by
  simp only [sllw_jolt_val, sllw_sail_operation]
  unfold jolt_virtual_pow2w_value
  rw [sllw_mul_eq_shift v1 v2]

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
        js'.sail = stateAfterWrite js.sail rd (sllw_sail_operation v1 v2) := by
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
  have h_mul_reads_rs1 :
      rX_bits rs1 js_afterPow2.sail = .ok v1 js_afterPow2.sail := by
    simpa only [js_afterPow2] using hok1
  obtain ⟨js_afterMul, h_mul_reads_rs1_again, h_mul_writes_product, h_mul_succeeds⟩ :=
    JoltISA.exists_jolt_state_after_mul_run_xreg_xreg_vreg rd rs1 (0 : JoltISA.VReg)
      js_afterPow2 v1 h_mul_reads_rs1

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SLLW result.
  let jolt_val := sllw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_reads_product,
      h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
      rd rd js_afterMul js.sail product hrd h_mul_writes_product

  -- Full program succeeds by stepping through the three instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.sllwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterPow2 h_pow2_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterPow2 js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, v1, v2, hok1, hok2, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLLW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    rw [h_sign_extend_writes_jolt_val, h_mul_writes_product]
    change stateAfterWrite (stateAfterWrite js.sail rd product) rd jolt_val =
      stateAfterWrite js.sail rd jolt_val
    exact stateAfterWrite_stateAfterWrite rd product jolt_val js.sail

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's three-instruction value is Sail's SLLW value.
  have h_sllw_value :
      jolt_val = sllw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact sllw_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sllw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail := by
  obtain ⟨js_afterSignExtend, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    sllwProgram_concrete rs2 rs1 rd hrd js hwf

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SLLW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SLLW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (sllw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sllw_sail_operation v1 v2) js.sail s' h_write).symm

end
