import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRA
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRA: Jolt VirtualSRA via bitmask = Sail SRA

Jolt program sequence:
1. `VirtualShiftRightBitmask v0, rs2` — compute the encoded shift bitmask
2. `VirtualSRA rd, rs1, v0` — arithmetic right shift by `ctz(bitmask)`
-/

-- NOTE: Math theorem: the Jolt bitmask SRA instruction computes Sail SRA.
private lemma virtual_sra_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    jolt_virtual_sra_value v1 (jolt_virtual_shift_right_bitmask_value v2) =
    shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  unfold shift_bits_right_arith LeanRV64D.Functions.log2_xlen
  congr 1

theorem execute_RTYPE_SRA_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind]

/-- Program-level concrete theorem for `SRA`.

The program-level proof mirrors `SRL`: first materialize the encoded shift
bitmask in scratch `v0`, then run the arithmetic virtual right shift that
consumes that scratch value. -/
theorem sraProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_right_arith v1
          (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
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

  -- Instruction 2: `VirtualSRA rd, rs1, v0` writes `raw` to `rd`.
  let raw := jolt_virtual_sra_value v1 bm
  have hread_rs1_from_mask : rX_bits rs1 js_mask.sail = .ok v1 js_mask.sail := by
    simpa [js_mask] using hok1
  obtain ⟨s', hrun_VirtualSRA, hw_raw_sra⟩ :=
    JoltISA.execInstr_virtualSRA_xreg_vreg_xreg_run_of_read rd rs1
      (0 : JoltISA.VReg) js_mask v1 hread_rs1_from_mask
  have hw_raw : wX_bits rd raw js.sail = .ok () s' := by
    simpa [js_mask, raw, bm] using hw_raw_sra
  let js' : SailJoltState := { sail := s', vregs := js_mask.vregs }
  have instr2_VirtualSRA_writes_raw :
      (JoltISA.execInstr (.VirtualSRA (.xreg rd) (.xreg rs1) (.vreg 0))).run js_mask =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSRA
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sraProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_mask
      instr1_VirtualShiftRightBitmask_writes_bm]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' instr2_VirtualSRA_writes_raw]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `virtual_sra_eq_shift` matches the virtual sequence with Sail SRA.
    have math_raw_shift :
        raw =
          shift_bits_right_arith v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
      dsimp [raw, bm]
      rw [virtual_sra_eq_shift]
    have final_write_from_initial :
        wX_bits rd
          (shift_bits_right_arith v1
            (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
          js.sail = .ok () s' := by
      rw [← math_raw_shift]
      exact hw_raw
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' final_write_from_initial

/-- Main program-level equivalence for `SRA`. -/
theorem sraProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SRA_factored rs2 rs1 rd)
    (sraProgram_concrete rs2 rs1 rd js hwf)

end
