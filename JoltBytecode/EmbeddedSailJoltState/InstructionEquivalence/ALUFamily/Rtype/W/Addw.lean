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

  -- Instruction 1: `ADD rd, rs1, rs2` writes `raw = v1 + v2` to `rd`.
  let raw := v1 + v2
  obtain ⟨s_raw, hrun_ADD, hw_raw⟩ :=
    JoltISA.execInstr_add_xreg_xreg_xreg_run_of_reads rd rs1 rs2 js v1 v2 hok1 hok2
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have instr1_ADD_writes_raw :
      (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_ADD

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw
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
  · unfold JoltISA.addwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw instr1_ADD_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr2_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `extractLsb_add` identifies `raw[31:0]` with word addition.
    have math_raw_low32 :
        final =
          sign_extend (m := 64)
            (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0) := by
      dsimp [final, raw]
      rw [extractLsb_add]
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

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
