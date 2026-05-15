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

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail MULW value
`h(v1, v2)`. -/
private theorem mulw_value_eq_sail (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * v2) 31 0) =
      sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))) := by
  congr 1
  rw [extractLsb_mul, ← mulw32_eq_mul]

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

  -- Instruction 1: `MUL rd, rs1, rs2` writes the 64-bit product to `rd`.
  let product := v1 * v2
  obtain ⟨s_afterMul, h_mul_run, h_mul_write⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 hok1 hok2
  have h_mul_writes_product : wX_bits rd product js.sail = .ok () s_afterMul := by
    simpa only [product] using h_mul_write
  let js_afterMul : SailJoltState := { sail := s_afterMul, vregs := js.vregs }
  have h_sail_after_mul :
      js_afterMul.sail = stateAfterWrite js.sail rd product := by
    simpa only [js_afterMul, product] using
      wX_bits_eq_stateAfterWrite rd product js.sail s_afterMul h_mul_writes_product
  have h_mul_succeeds :
      (JoltISA.execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterMul := by
    simpa only [js_afterMul] using h_mul_run

  have h_rd_reads_product : rX_bits rd s_afterMul = .ok product s_afterMul := by
    exact wX_rX_roundtrip rd product js.sail s_afterMul hrd h_mul_writes_product

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the MULW result.
  let mulwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb product 31 0)
  -- Math bridge for the completed Jolt value: the final Jolt value is Sail MULW.
  have h_mulw_result_eq_sail :
      mulwResult =
        sign_extend (m := 64)
          (to_bits_truncate (l := 32)
            (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
             BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))) := by
    simpa only [mulwResult, product] using mulw_value_eq_sail v1 v2
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterMul
      product (by simpa only [js_afterMul] using h_rd_reads_product)
  have h_sign_extend_writes_result :
      wX_bits rd mulwResult s_afterMul = .ok () s_afterSignExtend := by
    simpa only [js_afterMul, mulwResult] using h_sign_extend_write

  let js' : SailJoltState := { sail := s_afterSignExtend, vregs := js.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterMul.sail rd mulwResult := by
    simpa only [js', js_afterMul, mulwResult] using
      wX_bits_eq_stateAfterWrite rd mulwResult s_afterMul s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterMul =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  -- Full program succeeds by stepping through the two instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.mulwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js' h_sign_extend_succeeds]
    rfl

  -- Final Sail state: the second architectural write overwrites the first.
  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (to_bits_truncate (l := 32)
            (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
             BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))) :=
    sail_state_after_two_writes_eq_final rd
      js.sail js_afterMul.sail js'.sail
      product mulwResult
      (sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      h_sail_after_mul h_sail_after_sign_extend h_mulw_result_eq_sail

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

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
