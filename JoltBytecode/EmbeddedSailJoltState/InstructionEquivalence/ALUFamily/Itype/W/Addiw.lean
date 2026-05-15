import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.ADDI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

Jolt program sequence:
1. `ADDI rd, rs1, imm` — writes `v + sign_extend imm` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`
-/

theorem execute_ITYPE_ADDI_factored (imm : BitVec 12) (rs1 rd : regidx) :
  execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v ← rX_bits rs1
      wX_bits rd (v + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp [execute_ITYPE, bind_pure_comp]

theorem execute_ADDIW_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_ADDIW, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `ADDIW`.

The program is architectural `ADDI`, then `VirtualSignExtendWord rd, rd`.  As with the R-type
W proofs, the two architectural writes collapse to the final sign-extended
write. -/
theorem addiwProgram_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `ADDI rd, rs1, imm` writes the 64-bit sum to `rd`.
  let addResult := v + sign_extend (m := 64) imm
  obtain ⟨s_afterAddi, h_addi_run, h_addi_write⟩ :=
    JoltISA.exists_state_after_addi_run_xreg_xreg rd rs1 imm js v hok
  have h_addi_writes_result : wX_bits rd addResult js.sail = .ok () s_afterAddi := by
    simpa only [addResult] using h_addi_write
  let js_afterAddi : SailJoltState := { sail := s_afterAddi, vregs := js.vregs }
  have h_sail_after_addi :
      js_afterAddi.sail = stateAfterWrite js.sail rd addResult := by
    simpa only [js_afterAddi, addResult] using
      wX_bits_eq_stateAfterWrite rd addResult js.sail s_afterAddi h_addi_writes_result
  have h_addi_succeeds :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_afterAddi := by
    simpa only [js_afterAddi] using h_addi_run

  have h_rd_reads_add_result : rX_bits rd s_afterAddi = .ok addResult s_afterAddi := by
    exact wX_rX_roundtrip rd addResult js.sail s_afterAddi hrd h_addi_writes_result

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the ADDIW result.
  let addiwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb addResult 31 0)
  have h_addiw_result_eq_sail :
      addiwResult =
        sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0) := by
    dsimp only [addiwResult, addResult]
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterAddi
      addResult (by simpa only [js_afterAddi] using h_rd_reads_add_result)
  have h_sign_extend_writes_result :
      wX_bits rd addiwResult s_afterAddi = .ok () s_afterSignExtend := by
    simpa only [js_afterAddi, addiwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterAddi.sail rd addiwResult := by
    simpa only [js', js_afterAddi, addiwResult] using
      wX_bits_eq_stateAfterWrite rd addiwResult s_afterAddi s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterAddi =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.addiwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterAddi h_addi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAddi js' h_sign_extend_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)) := by
    calc
      js'.sail = stateAfterWrite js_afterAddi.sail rd addiwResult :=
        h_sail_after_sign_extend
      _ = stateAfterWrite (stateAfterWrite js.sail rd addResult) rd addiwResult := by
        rw [h_sail_after_addi]
      _ = stateAfterWrite js.sail rd addiwResult := by
        exact stateAfterWrite_stateAfterWrite rd addResult addiwResult js.sail
      _ = stateAfterWrite js.sail rd
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0)) := by
        rw [h_addiw_result_eq_sail]

  exact ⟨js', v, hok, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `ADDIW`. -/
theorem addiwProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.addiwProgram imm rs1 rd)).run js) =
    (execute_ADDIW imm rs1 rd).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
    (execute_ADDIW_factored imm rs1 rd)
    (addiwProgram_concrete imm rs1 rd hrd js hwf)

end
