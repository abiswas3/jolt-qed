import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Add
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.Add
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW

Jolt program sequence:
1. `ADD rd, rs1, rs2` — 64-bit add, writes `v1 + v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Sail's ADDW extracts lower 32 bits of each operand, adds them at 32
bits, and sign-extends to 64. The bridge lemma `extractLsb_add` (imported
from `ALUFamily/Bridges/Add.lean`) says truncation distributes over
addition, so both sides produce the same result.
-/

/-- Factoring: `execute_RTYPE rs2 rs1 rd rop.ADD` reads `rs1`, reads
`rs2`, writes `v1 + v2` to `rd`, returns `RETIRE_SUCCESS`. -/
theorem execute_RTYPE_ADD_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 + v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.ADDW` reads `rs1`, reads
`rs2`, writes `sext₆₄(v1[31:0] +₃₂ v2[31:0])` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_ADDW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail ADDW value
`h(v1, v2)`. -/
private theorem addw_value_eq_sail (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + v2) 31 0) =
      sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0) := by
  rw [extractLsb_add]

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

/-- Program-level concrete theorem for `ADDW`.

The new Jolt-ISA program states the Rust-style expansion directly:
architectural `ADD`, followed by the virtual sign-extend-word instruction.
The proof exposes the two real writes and collapses them to the final
sign-extended architectural write. -/
theorem addwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `ADD rd, rs1, rs2` writes the 64-bit sum to `rd`.
  let addResult := v1 + v2
  obtain ⟨s_afterAdd, h_add_run, h_add_write⟩ :=
    JoltISA.exists_state_after_add_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 hok1 hok2
  have h_add_writes_result : wX_bits rd addResult js.sail = .ok () s_afterAdd := by
    simpa only [addResult] using h_add_write
  let js_afterAdd : SailJoltState := { sail := s_afterAdd, vregs := js.vregs }
  have h_sail_after_add :
      js_afterAdd.sail = stateAfterWrite js.sail rd addResult := by
    simpa only [js_afterAdd, addResult] using
      wX_bits_eq_stateAfterWrite rd addResult js.sail s_afterAdd h_add_writes_result
  have h_add_succeeds :
      (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterAdd := by
    simpa only [js_afterAdd] using h_add_run

  have h_rd_reads_add_result : rX_bits rd s_afterAdd = .ok addResult s_afterAdd := by
    exact wX_rX_roundtrip rd addResult js.sail s_afterAdd hrd h_add_writes_result

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the ADDW result.
  let addwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb addResult 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail ADDW.
  have h_addw_result_eq_sail :
      addwResult =
        sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0) := by
    simpa only [addwResult, addResult] using addw_value_eq_sail v1 v2
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterAdd
      addResult (by simpa only [js_afterAdd] using h_rd_reads_add_result)
  have h_sign_extend_writes_result :
      wX_bits rd addwResult s_afterAdd = .ok () s_afterSignExtend := by
    simpa only [js_afterAdd, addwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterAdd.sail rd addwResult := by
    simpa only [js', js_afterAdd, addwResult] using
      wX_bits_eq_stateAfterWrite rd addwResult s_afterAdd s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterAdd =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  -- Full program succeeds by stepping through the two instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.addwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAdd h_add_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAdd js' h_sign_extend_succeeds]
    rfl

  -- Final Sail state: the second architectural write overwrites the first.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterAdd.sail js'.sail
      addResult addwResult
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      h_sail_after_add h_sail_after_sign_extend h_addw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `ADDW`. -/
theorem addwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)
    )
    (execute_RTYPEW_ADDW_factored rs2 rs1 rd)
    (addwProgram_concrete rs2 rs1 rd hrd js hwf)

end
