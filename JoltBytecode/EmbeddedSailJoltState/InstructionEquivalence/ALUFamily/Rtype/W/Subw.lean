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
  
  -- get v1 abd v2 and a proof that reads succeeded
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `SUB rd, rs1, rs2` writes `raw = v1 - v2` to `rd`.
  let raw := v1 - v2
  obtain ⟨s_raw, hrun_SUB, hw_raw⟩ :=
    JoltISA.execInstr_sub_xreg_xreg_xreg_run_of_reads rd rs1 rs2 js v1 v2 hok1 hok2
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have instr1_SUB_writes_raw :
      (JoltISA.execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_SUB

  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  let final :=
    sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
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
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.subwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw instr1_SUB_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr2_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `extractLsb_sub` identifies `raw[31:0]` with word subtraction.
    have math_raw_low32 :
        final =
          sign_extend (m := 64)
            (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0) := by
      dsimp [final, raw]
      rw [extractLsb_sub]
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

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
