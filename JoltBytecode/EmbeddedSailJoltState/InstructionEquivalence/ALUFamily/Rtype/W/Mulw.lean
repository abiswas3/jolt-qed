import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULW: Jolt MUL + VirtualSignExtendWord = Sail MULW

Jolt program sequence:
1. `MUL rd, rs1, rs2` — 64-bit multiply, writes `v1 * v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Sail's `MULW` is a standalone function `execute_MULW` rather than a branch
of `execute_RTYPEW`. The uniform R-type W closer still applies because the
surface shape is the same: read `rs1`, read `rs2`, write `rd`, return.

Bridge: `mulw32_eq_mul` (in `Bridges/Mul.lean`), connecting the Sail
`to_bits_truncate ∘ toInt` idiom to plain 32-bit `BitVec` multiply, and
`extractLsb_mul`, truncation distributing over multiply.
-/

theorem execute_MULW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      pure RETIRE_SUCCESS) := by
  simp only [execute_MULW]
  simp only [bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `MULW`.

The Jolt-ISA program records the inline sequence as ordinary 64-bit multiply
followed by sign-extension of the low word.  The pure bridge at the end
identifies that low-word multiply with Sail's signed 32-bit multiplication
encoding. -/
theorem mulwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (to_bits_truncate (l := 32)
            (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
             BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `MUL rd, rs1, rs2` writes `raw = v1 * v2` to `rd`.
  let raw := v1 * v2
  obtain ⟨s_raw, hrun_MUL, hw_raw⟩ :=
    JoltISA.execInstr_mul_xreg_xreg_xreg_run_of_reads rd rs1 rs2 js v1 v2 hok1 hok2
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have instr1_MUL_writes_raw :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_MUL

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
  · unfold JoltISA.mulwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw instr1_MUL_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr2_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `extractLsb_mul` and `mulw32_eq_mul` match Sail's word multiply.
    have math_raw_low32 :
        final =
          sign_extend (m := 64)
            (to_bits_truncate (l := 32)
              (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
               BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))) := by
      dsimp [final, raw]
      congr 1
      rw [extractLsb_mul, ← mulw32_eq_mul]
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64)
            (to_bits_truncate (l := 32)
              (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
               BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

/-- Main program-level equivalence for `MULW`. -/
theorem mulwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (to_bits_truncate (l := 32)
        (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
         BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
    (execute_MULW_factored rs2 rs1 rd)
    (mulwProgram_concrete rs2 rs1 rd hrd js hwf)

end
