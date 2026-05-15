import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLI: Jolt VirtualMULI = Sail SLLI

Jolt program sequence:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two
-/

private theorem extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp; rfl

private theorem mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat]

private theorem slli_mul_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ shamt.toNat) =
    shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [extractLsb_shamt6_id]
  exact mul_pow2_eq_shiftLeft v shamt

abbrev slli_sail_operation (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev slli_jolt_val (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  jolt_virtual_muli_value v (BitVec.ofNat 64 (2 ^ shamt.toNat))

private theorem slli_value_eq_sail (shamt : BitVec 6) (v : BitVec 64) :
    slli_jolt_val shamt v = slli_sail_operation shamt v := by
  simp only [slli_jolt_val, slli_sail_operation, jolt_virtual_muli_value]
  exact slli_mul_eq_shift v shamt

theorem execute_SHIFTIOP_SLLI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (slli_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp only [execute_SHIFTIOP]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, slli_sail_operation]

/-- Program-level concrete theorem for `SLLI`.

This is the theorem that the new architecture wants proofs to consume: the
left-hand side is the explicit Jolt-ISA program, not the older hand-written
monadic expansion. The instruction sequence is visible in the statement. -/
theorem slliProgram_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.slliProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (slli_sail_operation shamt v) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualMULI rd, rs1, 2^shamt` writes the shifted result to `rd`.
  let multiplier := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let jolt_val := slli_jolt_val shamt v
  obtain ⟨js_afterMuli, h_muli_reads_rs1, h_muli_writes_jolt_val,
      h_muli_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_muli_run_xreg_xreg rd rs1 multiplier js v hok

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.slliProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterMuli := by
    unfold JoltISA.slliProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMuli h_muli_succeeds]
    rfl

  refine ⟨js_afterMuli, v, h_muli_reads_rs1, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLLI value.
  have h_final_jolt_value :
      js_afterMuli.sail = stateAfterWrite js.sail rd jolt_val := by
    simp only [jolt_val, slli_jolt_val]
    exact h_muli_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's immediate multiply is Sail's SLLI value.
  have h_slli_value :
      jolt_val = slli_sail_operation shamt v := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact slli_value_eq_sail shamt v

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_slli_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SLLI`. -/
theorem slliProgram_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.slliProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run js.sail := by
  obtain ⟨js_afterMuli, v, h_read_rs1, h_program_succeeds, h_final_sail⟩ :=
    slliProgram_concrete shamt rs1 rd js hwf

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_SHIFTIOP_SLLI_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (slli_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (slli_sail_operation shamt v) js.sail s' h_write).symm

end
