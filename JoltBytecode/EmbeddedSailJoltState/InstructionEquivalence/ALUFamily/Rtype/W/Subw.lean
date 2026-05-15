import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Sub
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.Sub
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SUBW: Jolt SUB + VirtualSignExtendWord = Sail SUBW

Jolt program sequence:
1. `SUB rd, rs1, rs2` — 64-bit subtract, writes `v1 - v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Identical in shape to `ADDW`; the only differences are the operation
(`rop.SUB` / `ropw.SUBW`) and the bridge (`extractLsb_sub`).
-/

abbrev subw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)

abbrev subw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 - v2) 31 0)

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.SUBW` reads `rs1`, reads
`rs2`, writes `subw_sail_operation v1 v2` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_SUBW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (subw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, subw_sail_operation]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail SUBW value
`h(v1, v2)`. -/
private theorem subw_value_eq_sail (v1 v2 : BitVec 64) :
    subw_jolt_val v1 v2 = subw_sail_operation v1 v2 := by
  simp only [subw_jolt_val, subw_sail_operation]
  rw [extractLsb_sub]

/-- Program-level concrete theorem for `SUBW`.

The program is the same two-step shape as `ADDW`: do the 64-bit architectural
subtraction, then sign-extend the low word of `rd`. -/
theorem subwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
        rX_bits rs2 js.sail = .ok v2 js.sail ∧
        (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (subw_sail_operation v1 v2) := by
    obtain ⟨v1, hok1⟩ := hwf rs1
    obtain ⟨v2, hok2⟩ := hwf rs2

    -- Instruction 1: `SUB rd, rs1, rs2` writes the 64-bit difference to `rd`.
    let difference := v1 - v2
    obtain ⟨js_afterSub, h_sub_reads_rs1, h_sub_reads_rs2,
        h_sub_writes_difference, h_sub_succeeds⟩ :=
      JoltISA.exists_state_after_sub_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 hok1 hok2

    -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SUBW result.
    let jolt_val := subw_jolt_val v1 v2
    obtain ⟨js_afterSignExtend, h_sign_extend_reads_difference,
        h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
      JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
        rd rd js_afterSub js.sail difference hrd h_sub_writes_difference

    -- Full program succeeds by stepping through the two instruction runs.
    have h_program_succeeds :
        (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js_afterSignExtend := by
      unfold JoltISA.subwProgram
      rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub h_sub_succeeds]
      rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSub js_afterSignExtend
        h_sign_extend_succeeds]
      rfl

    refine ⟨js_afterSignExtend, v1, v2, h_sub_reads_rs1, h_sub_reads_rs2,
      h_program_succeeds, ?_⟩

    -- The instruction trace leaves `rd` containing the Jolt SUBW value.
    have h_final_jolt_value :
        js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
      rw [h_sign_extend_writes_jolt_val, h_sub_writes_difference]
      change stateAfterWrite (stateAfterWrite js.sail rd difference) rd jolt_val =
        stateAfterWrite js.sail rd jolt_val
      exact stateAfterWrite_stateAfterWrite rd difference jolt_val js.sail

    -- No more execution reasoning remains.
    -- The only real content left is the pure value equality:
    -- Jolt's two-instruction value is Sail's SUBW value.
    have h_subw_value :
        jolt_val = subw_sail_operation v1 v2 := by
      simp only [jolt_val]
      -- NOTE: The core math theorem.
      exact subw_value_eq_sail v1 v2

    -- After the value theorem, the final state claim is mechanical.
    rw [← h_subw_value]
    exact h_final_jolt_value

/-- Main program-level equivalence for `SUBW`. -/
theorem subwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail := by
  obtain ⟨js_afterSignExtend, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    subwProgram_concrete rs2 rs1 rd hrd js hwf

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SUBW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SUBW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (subw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (subw_sail_operation v1 v2) js.sail s' h_write).symm

end
