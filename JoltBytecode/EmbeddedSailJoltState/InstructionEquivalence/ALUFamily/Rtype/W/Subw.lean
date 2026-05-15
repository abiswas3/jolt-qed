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

/-
In English: 
The Sail Sub program is simply this monadic block.
-/ 
theorem execute_RTYPE_SUB_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 - v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-
In English: 
The Sail Subw program is simply this monadic block.
-/ 
theorem execute_RTYPEW_SUBW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail SUBW value
`h(v1, v2)`. -/
private theorem subw_value_eq_sail (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 - v2) 31 0) =
      sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0) := by
  rw [extractLsb_sub]

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
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `SUB rd, rs1, rs2` writes the 64-bit difference to `rd`.
  let subResult := v1 - v2
  obtain ⟨s_afterSub, h_sub_run, h_sub_write⟩ :=
    JoltISA.exists_state_after_sub_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 hok1 hok2
  have h_sub_writes_result : wX_bits rd subResult js.sail = .ok () s_afterSub := by
    simpa only [subResult] using h_sub_write
  let js_afterSub : SailJoltState := { sail := s_afterSub, vregs := js.vregs }
  have h_sail_after_sub :
      js_afterSub.sail = stateAfterWrite js.sail rd subResult := by
    simpa only [js_afterSub, subResult] using
      wX_bits_eq_stateAfterWrite rd subResult js.sail s_afterSub h_sub_writes_result
  have h_sub_succeeds :
      (JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    simpa only [js_afterSub] using h_sub_run

  have h_rd_reads_sub_result : rX_bits rd s_afterSub = .ok subResult s_afterSub := by
    exact wX_rX_roundtrip rd subResult js.sail s_afterSub hrd h_sub_writes_result

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SUBW result.
  let subwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb subResult 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail SUBW.
  have h_subw_result_eq_sail :
      subwResult =
        sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0) := by
    simpa only [subwResult, subResult] using subw_value_eq_sail v1 v2
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterSub
      subResult (by simpa only [js_afterSub] using h_rd_reads_sub_result)
  have h_sign_extend_writes_result :
      wX_bits rd subwResult s_afterSub = .ok () s_afterSignExtend := by
    simpa only [js_afterSub, subwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterSub.sail rd subwResult := by
    simpa only [js', js_afterSub, subwResult] using
      wX_bits_eq_stateAfterWrite rd subwResult s_afterSub s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterSub =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  -- Full program succeeds by stepping through the two instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.subwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub h_sub_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSub js' h_sign_extend_succeeds]
    rfl

  -- Final Sail state: the second architectural write overwrites the first.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterSub.sail js'.sail
      subResult subwResult
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
      h_sail_after_sub h_sail_after_sign_extend h_subw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SUBW`. -/
theorem subwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.subwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
    (execute_RTYPEW_SUBW_factored rs2 rs1 rd)
    (subwProgram_concrete rs2 rs1 rd hrd js hwf)

end
