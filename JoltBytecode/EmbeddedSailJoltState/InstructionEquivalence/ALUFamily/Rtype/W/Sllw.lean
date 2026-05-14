import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLW: VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt decomposes SLLW into (from `BytecodeExpansions/Sllw.lean`):

1. `VirtualPow2W v_pow, rs2` — compute `2 ^ (rs2[4:0])` into v0
2. `MUL rd, rs1, v_pow` — multiply rs1 by the power of two
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits

Bridge: `sllw_mul_eq_shift` (in `Bridges/Shift.lean`).
-/

theorem execute_RTYPEW_SLLW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `SLLW`.

The expansion is `VirtualPow2W` into scratch `v0`, a real-destination
multiply by that scratch value, then `SExtW` on `rd`. -/
theorem sllwProgram_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
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
  let vp := jolt_virtual_pow2w_value v2
  let js_pow : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then vp else js.vregs r }
  have hpow :
      (JoltISA.execInstr (.VirtualPow2W (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_pow := by
    simpa [js_pow, vp] using
      (JoltISA.execInstr_virtualPow2W_xreg_vreg_run
        (0 : JoltISA.VReg) rs2 js v2 hok2)
  let raw := v1 * vp
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_pow.vregs }
  have hmul :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_pow =
        .ok RETIRE_SUCCESS js_raw := by
    have hread : rX_bits rs1 js_pow.sail = .ok v1 js_pow.sail := by
      simpa [js_pow] using hok1
    have hwrite : wX_bits rd (v1 * js_pow.vregs (0 : JoltISA.VReg)) js_pow.sail =
        .ok () s_raw := by
      simpa [js_pow, raw, vp] using hw_raw
    simpa [js_raw] using
      (JoltISA.execInstr_mul_xreg_xreg_vreg_run rd rs1 (0 : JoltISA.VReg)
        js_pow v1 s_raw hread hwrite)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final :=
    sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js_pow.vregs }
  have hsextw :
      (JoltISA.execInstr (.SExtW (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sllwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_pow hpow]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_pow js_raw hmul]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw, vp, jolt_virtual_pow2w_value]
    rw [sllw_mul_eq_shift v1 v2]

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
    (execute_RTYPEW_SLLW_factored rs2 rs1 rd)
    (sllwProgram_concrete rs2 rs1 rd hrd js hwf)

end
