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

theorem execute_RTYPEW_SLLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind]

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
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `VirtualPow2W v0, rs2` writes `vp = 2 ^ rs2[4:0]` to `v0`.
  let vp := jolt_virtual_pow2w_value v2
  let js_pow : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then vp else js.vregs r }
  have instr1_VirtualPow2W_writes_vp :
      (JoltISA.execInstr (.VirtualPow2W (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_pow := by
    simpa [js_pow, vp] using
      (JoltISA.execInstr_virtualPow2W_xreg_vreg_run
        (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `MUL rd, rs1, v0` writes `raw = v1 * vp` to `rd`.
  let raw := v1 * vp
  have hread_rs1_from_pow : rX_bits rs1 js_pow.sail = .ok v1 js_pow.sail := by
    simpa [js_pow] using hok1
  obtain ⟨s_raw, hrun_MUL, hw_raw_mul⟩ :=
    JoltISA.execInstr_mul_xreg_xreg_vreg_run_of_read rd rs1 (0 : JoltISA.VReg)
      js_pow v1 hread_rs1_from_pow
  have hw_raw : wX_bits rd raw js.sail = .ok () s_raw := by
    simpa [js_pow, raw, vp] using hw_raw_mul
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_pow.vregs }
  have instr2_MUL_writes_raw :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_pow =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_MUL

  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  let final :=
    sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hrun_VirtualSignExtendWord, hw_final_raw⟩ :=
    JoltISA.execInstr_sextw_xreg_xreg_run_of_read rd rd js_raw raw
      (by simpa [js_raw] using hread_rd)
  have hw_final : wX_bits rd final s_raw = .ok () s_final := by
    simpa [js_raw, final] using hw_final_raw

  let js' : SailJoltState := { sail := s_final, vregs := js_pow.vregs }
  have instr3_VirtualSignExtendWord_writes_final :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSignExtendWord
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sllwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_pow instr1_VirtualPow2W_writes_vp]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_pow js_raw instr2_MUL_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr3_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `sllw_mul_eq_shift` matches pow2 multiplication with Sail SLLW.
    have math_raw_low32 :
        final =
          sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
            (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
      dsimp [final, raw, vp, jolt_virtual_pow2w_value]
      rw [sllw_mul_eq_shift v1 v2]
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
            (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SLLW_factored rs2 rs1 rd)
    (sllwProgram_concrete rs2 rs1 rd hrd js hwf)

end
