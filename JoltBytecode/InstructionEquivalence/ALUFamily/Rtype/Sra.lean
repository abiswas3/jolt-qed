import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRA
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift

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

abbrev sra_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  shift_bits_right_arith v1
    (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev sra_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  jolt_virtual_sra_value v1 (jolt_virtual_shift_right_bitmask_value v2)

private theorem sra_value_eq_sail (v1 v2 : BitVec 64) :
    sra_jolt_val v1 v2 = sra_sail_operation v1 v2 := by
  simp only [sra_jolt_val, sra_sail_operation]
  exact virtual_sra_eq_shift v1 v2

theorem execute_RTYPE_SRA_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sra_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, sra_sail_operation]

/-- Program-level concrete theorem for `SRA`.

The program-level proof mirrors `SRL`: first materialize the encoded shift
bitmask in scratch `v0`, then run the arithmetic virtual right shift that
consumes that scratch value. -/
theorem sraProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (sra_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes the shift bitmask to `v0`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value v2
  obtain ⟨js_afterBitmask, h_bitmask_reads_rs2, h_bitmask_keeps_sail,
      h_bitmask_writes_shiftBitmask, _, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_xreg
      (0 : JoltISA.VReg) rs2 js v2 h_read_rs2

  -- Instruction 2: `VirtualSRA rd, rs1, v0` writes the shifted result to `rd`.
  let jolt_val := sra_jolt_val v1 v2
  obtain ⟨js_afterSra, h_virtual_sra_reads_rs1, h_virtual_sra_writes_jolt_val,
      h_virtual_sra_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sra_run_xreg_xreg_vreg_of_value
      rd rs1 (0 : JoltISA.VReg) js_afterBitmask js.sail v1 shiftBitmask
      h_bitmask_keeps_sail h_read_rs1 h_bitmask_writes_shiftBitmask

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSra := by
    unfold JoltISA.sraProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterBitmask h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSra
      h_virtual_sra_succeeds]
    rfl

  refine ⟨js_afterSra, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRA value.
  have h_final_jolt_value :
      js_afterSra.sail = stateAfterWrite js.sail rd jolt_val := by
    change js_afterSra.sail = stateAfterWrite js.sail rd jolt_val
    exact h_virtual_sra_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SRA value.
  have h_sra_value :
      jolt_val = sra_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact sra_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sra_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRA`. -/
theorem sraProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.sraProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sraProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_RTYPE_SRA_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSra, h_program_succeeds, h_final_sail⟩ :=
    sraProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_RTYPE_SRA_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (sra_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sra_sail_operation v1 v2) js.sail s' h_write).symm

end
