import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRA: Jolt VirtualSRA via bitmask = Sail SRA

Same bitmask encoding as SRL but with arithmetic (sign-extending) right
shift.
-/

private lemma virtual_sra_eq_shift (v1 v2 : BitVec 64) :
    jolt_virtual_sra_value v1 (jolt_virtual_shift_right_bitmask_value v2) =
    shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  unfold shift_bits_right_arith LeanRV64D.Functions.log2_xlen
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb]
  congr 1

theorem execute_RTYPE_SRA_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (shift_bits_right_arith v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

/-- Program-level concrete theorem for `SRA`.

The program-level proof mirrors `SRL`: first materialize the encoded shift
bitmask in scratch `v0`, then run the arithmetic virtual right shift that
consumes that scratch value. -/
theorem sraProgram_concrete (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
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
  let bm := jolt_virtual_shift_right_bitmask_value v2
  obtain ⟨s', hw⟩ := wX_shape rd (jolt_virtual_sra_value v1 bm) js.sail
  let js_mask : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then bm else js.vregs r }
  let js' : SailJoltState := { sail := s', vregs := js_mask.vregs }
  have hmask :
      (JoltISA.execInstr (.VirtualShiftRightBitmask (.vreg 0) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_mask := by
    simpa [js_mask, bm] using
      (JoltISA.execInstr_virtualShiftRightBitmask_xreg_vreg_run
        (0 : JoltISA.VReg) rs2 js v2 hok2)
  have hsra :
      (JoltISA.execInstr (.VirtualSRA (.xreg rd) (.xreg rs1) (.vreg 0))).run js_mask =
        .ok RETIRE_SUCCESS js' := by
    have hread : rX_bits rs1 js_mask.sail = .ok v1 js_mask.sail := by
      simpa [js_mask] using hok1
    have hwrite :
        wX_bits rd (jolt_virtual_sra_value v1 (js_mask.vregs (0 : JoltISA.VReg)))
          js_mask.sail = .ok () s' := by
      simpa [js_mask, bm] using hw
    simpa [js'] using
      (JoltISA.execInstr_virtualSRA_xreg_vreg_xreg_run rd rs1 (0 : JoltISA.VReg)
        js_mask v1 s' hread hwrite)
  refine ⟨js', v1, v2, hok1, hok2, ?_, ?_⟩
  · unfold JoltISA.sraProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_mask hmask]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_mask js' hsra]
    rfl
  · dsimp [js']
    rw [← virtual_sra_eq_shift v1 v2]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Main program-level equivalence for `SRA`. -/
theorem sraProgram_eq_sail (rs2 rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_RTYPE_SRA_factored rs2 rs1 rd)
    (sraProgram_concrete rs2 rs1 rd js hwf)

end
