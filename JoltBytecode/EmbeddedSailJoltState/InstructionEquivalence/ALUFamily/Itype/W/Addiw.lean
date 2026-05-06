import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

Jolt's ADDIW is `execute_ITYPE iop.ADDI + VSEW`. No bridge lemma is
needed: both Jolt and Sail compute the same value
`sign_extend(extractLsb(v + sign_extend(imm)))` for the final value in
`rd`.
-/

theorem execute_ITYPE_ADDI_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v ← rX_bits rs1
      wX_bits rd (v + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp [execute_ITYPE, bind_pure_comp, pure_bind]

theorem execute_ADDIW_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v + sign_extend (m := 64) imm) 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_ADDIW, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `ADDIW`.

The program is architectural `ADDI`, then `SExtW rd, rd`.  As with the R-type
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
  let raw := v + sign_extend (m := 64) imm
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have haddi :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw, raw] using
      (JoltISA.execInstr_addi_xreg_xreg_run rd rs1 imm js v s_raw hok hw_raw)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js.vregs }
  have hsextw :
      (JoltISA.execInstr (.SExtW (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.addiwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw haddi]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc

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
