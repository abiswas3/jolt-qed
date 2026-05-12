import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Add
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW

Jolt decomposes ADDW as:
1. `execute_RTYPE rop.ADD` — 64-bit add, writes `v1 + v2` to `rd`
2. `VirtualSignExtendWord rd` — sign-extend lower 32 bits of `rd`

Sail's ADDW extracts lower 32 bits of each operand, adds them at 32
bits, and sign-extends to 64. The bridge lemma `extractLsb_add` (imported
from `ALUFamily/Bridges/Add.lean`) says truncation distributes over
addition, so both sides produce the same result.
-/

/-- Factoring: `execute_RTYPE rs2 rs1 rd rop.ADD` reads `rs1`, reads
`rs2`, writes `v1 + v2` to `rd`, returns `RETIRE_SUCCESS`. -/
theorem execute_RTYPE_ADD_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 + v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.ADDW` reads `rs1`, reads
`rs2`, writes `sext₆₄(v1[31:0] +₃₂ v2[31:0])` to `rd`, returns
`RETIRE_SUCCESS`. 
All this does is write the Sail code as do program.
I am not sure we need this as much anymore (TODO:) 
-/
theorem execute_RTYPEW_ADDW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `ADDW`.

The new Jolt-ISA program states the Rust-style expansion directly:
architectural `ADD`, followed by the virtual sign-extend-word instruction.
The proof exposes the two real writes and collapses them to the final
sign-extended architectural write. -/
theorem addwProgram_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
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
  let raw := v1 + v2
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js.vregs }
  have hadd :
      (JoltISA.execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw, raw] using
      (JoltISA.execInstr_add_xreg_xreg_xreg_run rd rs1 rs2
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
  · unfold JoltISA.addwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_raw hadd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [← extractLsb_add v1 v2]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc

/-- Main program-level equivalence for `ADDW`. -/
theorem addwProgram_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.addwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)
    )
    (execute_RTYPEW_ADDW_factored rs2 rs1 rd)
    (addwProgram_concrete rs2 rs1 rd hrd js hwf)

end
