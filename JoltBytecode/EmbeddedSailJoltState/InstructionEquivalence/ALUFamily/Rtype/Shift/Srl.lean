import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRL: Jolt VirtualSRL via bitmask = Sail SRL

Jolt program sequence:
1. `VirtualShiftRightBitmask v0, rs2` — compute the encoded shift bitmask
2. `VirtualSRL rd, rs1, bitmask` — logical right shift by `ctz(bitmask)`

`ctz(bitmask) = rs2[5:0]`, so this matches Sail's SRL.
-/

-- NOTE: Math theorem: the Jolt bitmask SRL instruction computes Sail SRL.
private lemma virtual_srl_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    jolt_virtual_srl_value v1 (jolt_virtual_shift_right_bitmask_value v2) =
    shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold jolt_virtual_srl_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  unfold shift_bits_right LeanRV64D.Functions.log2_xlen
  congr 1

theorem execute_RTYPE_SRL_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Program-level concrete theorem for `SRL`.

The program first writes the virtual right-shift bitmask for `rs2` into
scratch `v0`; the second instruction consumes that scratch value with
`VirtualSRL` and writes the real destination. -/
theorem srlProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes the shift bitmask to `v0`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value v2
  let js_afterBitmask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then shiftBitmask else js.vregs r }
  have h_bitmask_succeeds :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterBitmask := by
    simpa only [js_afterBitmask, shiftBitmask] using
      (JoltISA.virtual_shift_right_bitmask_run_vreg_xreg
        (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `VirtualSRL rd, rs1, v0` writes the shifted result to `rd`.
  let shiftedResult := jolt_virtual_srl_value v1 shiftBitmask
  have h_rs1_reads_v1_after_bitmask :
      rX_bits rs1 js_afterBitmask.sail = .ok v1 js_afterBitmask.sail := by
    simpa only [js_afterBitmask] using hok1
  obtain ⟨s_afterSrl, h_virtual_srl_run, h_virtual_srl_write⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_xreg_vreg rd rs1
      (0 : JoltISA.VReg) js_afterBitmask v1 h_rs1_reads_v1_after_bitmask
  have h_srl_writes_shifted_result :
      wX_bits rd shiftedResult js.sail = .ok () s_afterSrl := by
    simpa only [js_afterBitmask, shiftedResult, shiftBitmask] using h_virtual_srl_write
  let js' : SailJoltState := { sail := s_afterSrl, vregs := js_afterBitmask.vregs }
  have h_virtual_srl_succeeds :
      (JoltISA.execInstr (.VirtualSRL (.xreg rd) (.xreg rs1) (.vreg 0))).run
        js_afterBitmask =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_virtual_srl_run

  -- Math bridge: the virtual bitmask SRL value is Sail SRL.
  have h_shifted_result_eq_sail :
      shiftedResult =
        shift_bits_right v1
          (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
    dsimp only [shiftedResult, shiftBitmask]
    rw [virtual_srl_eq_shift]

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.srlProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterBitmask h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js'
      h_virtual_srl_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right v1
          (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
    calc
      js'.sail = stateAfterWrite js.sail rd shiftedResult := by
        simpa only [js'] using
          wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterSrl
            h_srl_writes_shifted_result
      _ = stateAfterWrite js.sail rd
            (shift_bits_right v1
              (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
        rw [h_shifted_result_eq_sail]

  exact ⟨js', v1, v2, hok1, hok2, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SRL`. -/
theorem srlProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRL).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_right v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SRL_factored rs2 rs1 rd)
    (srlProgram_concrete rs2 rs1 rd js hwf)

end
