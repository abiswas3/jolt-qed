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

  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes `bm` to `v0`.
  let bm := jolt_virtual_shift_right_bitmask_value v2
  let js_mask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then bm else js.vregs r }
  have instr1_VirtualShiftRightBitmask_writes_bm :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, bm] using
      (JoltISA.execInstr_virtualShiftRightBitmask_xreg_vreg_run
        (0 : JoltISA.VReg) rs2 js v2 hok2)

  -- Instruction 2: `VirtualSRL rd, rs1, v0` writes `raw` to `rd`.
  let raw := jolt_virtual_srl_value v1 bm
  have hread_rs1_from_mask : rX_bits rs1 js_mask.sail = .ok v1 js_mask.sail := by
    simpa [js_mask] using hok1
  obtain ⟨s', hrun_VirtualSRL, hw_raw_srl⟩ :=
    JoltISA.execInstr_virtualSRL_xreg_vreg_xreg_run_of_read rd rs1
      (0 : JoltISA.VReg) js_mask v1 hread_rs1_from_mask
  have hw_raw : wX_bits rd raw js.sail = .ok () s' := by
    simpa [js_mask, raw, bm] using hw_raw_srl
  let js' : SailJoltState := { sail := s', vregs := js_mask.vregs }
  have instr2_VirtualSRL_writes_raw :
      (JoltISA.execInstr (.VirtualSRL (.xreg rd) (.xreg rs1) (.vreg 0))).run js_mask =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSRL
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.srlProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_mask
      instr1_VirtualShiftRightBitmask_writes_bm]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' instr2_VirtualSRL_writes_raw]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `virtual_srl_eq_shift` matches the virtual sequence with Sail SRL.
    have math_raw_shift :
        raw =
          shift_bits_right v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
      dsimp [raw, bm]
      rw [virtual_srl_eq_shift]
    have final_write_from_initial :
        wX_bits rd
          (shift_bits_right v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
          js.sail = .ok () s' := by
      rw [← math_raw_shift]
      exact hw_raw
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' final_write_from_initial

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
