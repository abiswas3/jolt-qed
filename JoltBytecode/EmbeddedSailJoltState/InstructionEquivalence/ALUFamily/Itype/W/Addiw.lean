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

  -- Instruction 1: `ADDI rd, rs1, imm` writes `raw = v + sign_extend imm` to `rd`.
  let raw := v + sign_extend (m := 64) imm
  obtain ⟨s_raw, hrun_ADDI, hw_raw⟩ :=
    JoltISA.execInstr_addi_xreg_xreg_run_of_read rd rs1 imm js v hok
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have instr1_ADDI_writes_raw :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_ADDI

  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hrun_VirtualSignExtendWord, hw_final_raw⟩ :=
    JoltISA.execInstr_sextw_xreg_xreg_run_of_read rd rd js_raw raw
      (by simpa [js_raw] using hread_rd)
  have hw_final : wX_bits rd final s_raw = .ok () s_final := by
    simpa [js_raw, final] using hw_final_raw

  let js' : SailJoltState := { sail := s_final, vregs := js.vregs }
  have instr2_VirtualSignExtendWord_writes_final :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSignExtendWord
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.addiwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw instr1_ADDI_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr2_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: no bridge is needed; `final` is the Sail ADDIW value by definition.
    have math_raw_low32 :
        final =
          sign_extend (m := 64)
            (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0) := by
      dsimp [final, raw]
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

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
