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

/-- The value written by the first Jolt instruction in the ADDW expansion. -/
private def addwRawValue (v1 v2 : BitVec 64) : BitVec 64 :=
  v1 + v2

/-- The value written by the second Jolt instruction in the ADDW expansion. -/
private def addwSextwValue (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (addwRawValue v1 v2) 31 0)

/-- The value written by Sail's ADDW instruction. -/
private def sailAddwValue (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail ADDW value
`h(v1, v2)`. -/
private theorem addwSextwValue_eq_sailAddwValue (v1 v2 : BitVec 64) :
    addwSextwValue v1 v2 = sailAddwValue v1 v2 := by
  unfold addwSextwValue addwRawValue sailAddwValue
  rw [extractLsb_add]

/-- Two writes to the same architectural destination collapse to Sail's ADDW
write once the value-level bridge has identified the final value. -/
private theorem addw_two_writes_eq_sail_write
    (rd : regidx) (s : SailState) (v1 v2 : BitVec 64) :
    stateAfterWrite (stateAfterWrite s rd (addwRawValue v1 v2)) rd
        (addwSextwValue v1 v2) =
      stateAfterWrite s rd (sailAddwValue v1 v2) := by
  calc
    stateAfterWrite (stateAfterWrite s rd (addwRawValue v1 v2)) rd
        (addwSextwValue v1 v2)
        = stateAfterWrite s rd (addwSextwValue v1 v2) := by
            exact stateAfterWrite_stateAfterWrite rd (addwRawValue v1 v2)
              (addwSextwValue v1 v2) s
    _ = stateAfterWrite s rd (sailAddwValue v1 v2) := by
            rw [addwSextwValue_eq_sailAddwValue]

/-- Close the program-run plumbing once the two ADDW expansion instructions
have been shown to retire in sequence. -/
private theorem addwProgram_run_of_instrs
    (rs2 rs1 rd : regidx)
    (js js_raw js' : SailJoltState)
    (h_add :
      (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw)
    (h_sextw :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js') :
    (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
      .ok RETIRE_SUCCESS js' := by
  unfold JoltISA.addwProgram
  rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw h_add]
  rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' h_sextw]
  rfl

/-- Semantic step for the first ADDW expansion instruction.

The architectural `ADD` retires, preserves virtual registers, updates the Sail
state with `v1 + v2`, and because `rd ≠ x0`, reading `rd` afterwards returns
that value. -/
private theorem addw_add_step
    (rd rs1 rs2 : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    ∃ js_afterAdd,
      (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterAdd ∧
      js_afterAdd.vregs = js.vregs ∧
      js_afterAdd.sail = stateAfterWrite js.sail rd (addwRawValue v1 v2) ∧
      rX_bits rd js_afterAdd.sail = .ok (addwRawValue v1 v2) js_afterAdd.sail := by
  obtain ⟨s_afterAdd, hrun, hwrite⟩ :=
    JoltISA.execInstr_add_xreg_xreg_xreg_run_of_reads rd rs1 rs2 js v1 v2 hrs1 hrs2
  refine ⟨{ sail := s_afterAdd, vregs := js.vregs }, ?_, rfl, ?_, ?_⟩
  · simpa using hrun
  · simpa [addwRawValue] using
      wX_bits_eq_stateAfterWrite rd (v1 + v2) js.sail s_afterAdd hwrite
  · simpa [addwRawValue] using
      wX_rX_roundtrip rd (v1 + v2) js.sail s_afterAdd hrd hwrite

/-- Semantic step for the second ADDW expansion instruction.

`VirtualSignExtendWord rd, rd` retires, preserves virtual registers, and writes
`g(f(v1, v2))` to `rd` in the Sail state. -/
private theorem addw_sextw_step
    (rd : regidx)
    (js_afterAdd : SailJoltState)
    (v1 v2 : BitVec 64)
    (hread : rX_bits rd js_afterAdd.sail =
      .ok (addwRawValue v1 v2) js_afterAdd.sail) :
    ∃ js_afterSextw,
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterAdd =
        .ok RETIRE_SUCCESS js_afterSextw ∧
      js_afterSextw.vregs = js_afterAdd.vregs ∧
      js_afterSextw.sail =
        stateAfterWrite js_afterAdd.sail rd (addwSextwValue v1 v2) := by
  obtain ⟨s_afterSextw, hrun, hwrite⟩ :=
    JoltISA.execInstr_sextw_xreg_xreg_run_of_read rd rd js_afterAdd
      (addwRawValue v1 v2) hread
  refine ⟨{ sail := s_afterSextw, vregs := js_afterAdd.vregs }, ?_, rfl, ?_⟩
  · simpa using hrun
  · simpa [addwSextwValue] using
      wX_bits_eq_stateAfterWrite rd _ js_afterAdd.sail s_afterSextw hwrite

/-- Run the complete two-instruction ADDW expansion from already-known source
reads.

This is the human proof as an API lemma:

* first instruction gives a state where `rd = f(v1, v2)`;
* second instruction gives a state where `rd = g(f(v1, v2))`;
* the math bridge says `g(f(v1, v2)) = h(v1, v2)`;
* the two architectural writes collapse to one final Sail ADDW write. -/
private theorem addwProgram_run_of_reads
    (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    ∃ js',
      (JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sailAddwValue v1 v2) := by
  -- First instruction: `ADD rd, rs1, rs2` writes `f(v1, v2)`.
  obtain ⟨js_afterAdd, hrun_add, _, hsail_afterAdd, hread_add⟩ :=
    addw_add_step rd rs1 rs2 hrd js v1 v2 hrs1 hrs2

  -- Second instruction: `VirtualSignExtendWord rd, rd` writes `g(f(v1, v2))`.
  obtain ⟨js_afterSextw, hrun_sextw, _, hsail_afterSextw⟩ :=
    addw_sextw_step rd js_afterAdd v1 v2 hread_add

  refine ⟨js_afterSextw, ?_, ?_⟩
  · exact addwProgram_run_of_instrs rs2 rs1 rd js js_afterAdd js_afterSextw
      hrun_add hrun_sextw
  · calc
      js_afterSextw.sail
          = stateAfterWrite js_afterAdd.sail rd (addwSextwValue v1 v2) :=
              hsail_afterSextw
      _ = stateAfterWrite (stateAfterWrite js.sail rd (addwRawValue v1 v2)) rd
            (addwSextwValue v1 v2) := by
              rw [hsail_afterAdd]
      _ = stateAfterWrite js.sail rd (sailAddwValue v1 v2) := by
              exact addw_two_writes_eq_sail_write rd js.sail v1 v2

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

  -- The helper is the readable proof:
  -- ADD writes `f(v1, v2)`, SEXTW writes `g(f(v1, v2))`,
  -- and the ADDW bridge identifies that value with Sail's `h(v1, v2)`.
  obtain ⟨js', hrun, hsail⟩ :=
    addwProgram_run_of_reads rs2 rs1 rd hrd js v1 v2 hok1 hok2
  refine ⟨js', v1, v2, hok1, hok2, hrun, ?_⟩
  simpa [sailAddwValue] using hsail

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
