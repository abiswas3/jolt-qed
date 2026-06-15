import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift

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

abbrev srl_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev srl_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  jolt_virtual_srl_value v1 (jolt_virtual_shift_right_bitmask_value v2)

private theorem srl_value_eq_sail (v1 v2 : BitVec 64) :
    srl_jolt_val v1 v2 = srl_sail_operation v1 v2 := by
  simp only [srl_jolt_val, srl_sail_operation]
  exact virtual_srl_eq_shift v1 v2

theorem execute_RTYPE_SRL_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (srl_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, srl_sail_operation]

/-- Program-level concrete theorem for `SRL`.

The program first writes the virtual right-shift bitmask for `rs2` into
scratch `v0`; the second instruction consumes that scratch value with
`VirtualSRL` and writes the real destination. -/
theorem srlProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (srl_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes the shift bitmask to `v0`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value v2
  obtain ⟨js_afterBitmask, h_bitmask_reads_rs2, h_bitmask_keeps_sail,
      h_bitmask_writes_shiftBitmask, _, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_xreg
      JoltISA.inlineTmp0 rs2 js v2 h_read_rs2

  -- Instruction 2: `VirtualSRL rd, rs1, v0` writes the shifted result to `rd`.
  let jolt_val := srl_jolt_val v1 v2
  obtain ⟨js_afterSrl, h_virtual_srl_reads_rs1, h_virtual_srl_writes_jolt_val,
      h_virtual_srl_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_xreg_vreg_of_value
      rd rs1 JoltISA.inlineTmp0 js_afterBitmask js.sail v1 shiftBitmask
      h_bitmask_keeps_sail h_read_rs1 h_bitmask_writes_shiftBitmask

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSrl := by
    unfold JoltISA.srlProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterBitmask h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSrl
      h_virtual_srl_succeeds]
    rfl

  refine ⟨js_afterSrl, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRL value.
  have h_final_jolt_value :
      js_afterSrl.sail = stateAfterWrite js.sail rd jolt_val := by
    change js_afterSrl.sail = stateAfterWrite js.sail rd jolt_val
    exact h_virtual_srl_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SRL value.
  have h_srl_value :
      jolt_val = srl_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact srl_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srl_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRL`. -/
theorem srlProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    projectResult ((JoltISA.execProgram (JoltISA.srlProgram rs2 rs1 rd)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRL).run js.sail := by
  let v1 := h.rs1_val
  let v2 := h.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read.value_eq
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read.value_eq
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srlProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_RTYPE_SRL_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSrl, h_program_succeeds, h_final_sail⟩ :=
    srlProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_RTYPE_SRL_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (srl_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (srl_sail_operation v1 v2) js.sail s' h_write).symm

end
