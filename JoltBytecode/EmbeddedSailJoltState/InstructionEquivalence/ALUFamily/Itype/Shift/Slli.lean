import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

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

theorem execute_SHIFTIOP_SLLI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

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
      js'.sail = stateAfterWrite js.sail rd
        (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualMULI rd, rs1, 2^shamt` writes `raw` to `rd`.
  let imm := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let raw := jolt_virtual_muli_value v imm
  obtain ⟨s', hrun_VirtualMULI, hw_raw⟩ :=
    JoltISA.execInstr_virtualMULI_xreg_xreg_run_of_read rd rs1 imm js v hok
  let js' : SailJoltState := { sail := s', vregs := js.vregs }
  have instr1_VirtualMULI_writes_raw :
      (JoltISA.execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualMULI
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.slliProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' instr1_VirtualMULI_writes_raw]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `slli_mul_eq_shift` matches pow2 multiplication with Sail SLLI.
    have math_raw_shift :
        raw =
          shift_bits_left v
            (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
      dsimp [raw, imm, jolt_virtual_muli_value]
      rw [slli_mul_eq_shift]
    have final_write_from_initial :
        wX_bits rd
          (shift_bits_left v
            (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
          js.sail = .ok () s' := by
      rw [← math_raw_shift]
      exact hw_raw
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' final_write_from_initial

/-- Main program-level equivalence for `SLLI`. -/
theorem slliProgram_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.slliProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => shift_bits_left v
      (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
    (execute_SHIFTIOP_SLLI_factored shamt rs1 rd)
    (slliProgram_concrete shamt rs1 rd js hwf)

end
