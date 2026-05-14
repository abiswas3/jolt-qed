import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Mul
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULW: Jolt MUL + VirtualSignExtendWord = Sail MULW

Sail's `MULW` is a standalone function `execute_MULW` rather than a branch
of `execute_RTYPEW`. The uniform R-type W closer still applies because the
surface shape is the same: read `rs1`, read `rs2`, write `rd`, return.

Bridge: `mulw32_eq_mul` (in `Bridges/Mul.lean`), connecting the Sail
`to_bits_truncate ∘ toInt` idiom to plain 32-bit `BitVec` multiply, and
`extractLsb_mul`, truncation distributing over multiply.
-/

theorem execute_MULW_factored (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      pure RETIRE_SUCCESS) := by
  simp [execute_MULW, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `MULW`.

The Jolt-ISA program records the inline sequence as ordinary 64-bit multiply
followed by sign-extension of the low word.  The pure bridge at the end
identifies that low-word multiply with Sail's signed 32-bit multiplication
encoding. -/
theorem mulwProgram_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
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
  let raw := v1 * v2
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have hmul :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw, raw] using
      (JoltISA.execInstr_mul_xreg_xreg_xreg_run rd rs1 rs2
        js v1 v2 s_raw hok1 hok2 hw_raw)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final :=
    sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js.vregs }
  have hsextw :
      (JoltISA.execInstr (.SExtW (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.mulwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw hmul]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw]
    congr 1
    congr 1
    rw [extractLsb_mul, ← mulw32_eq_mul]

/-- Main program-level equivalence for `MULW`. -/
theorem mulwProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
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
