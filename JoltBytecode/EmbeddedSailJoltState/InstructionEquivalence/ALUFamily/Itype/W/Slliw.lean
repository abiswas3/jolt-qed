import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLIW: Jolt VirtualMULI + VSEW = Sail SLLIW

Jolt program sequence:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two (= left shift)
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The bridge `extractLsb_mul_pow2` is specific to SLLIW (scalar shamt)
rather than the R-type variant; kept inline here since no other
instruction reuses it.
-/

private theorem extractLsb_mul_pow2 (v : BitVec 64) (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0 =
    shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt := by
  unfold shift_bits_left Sail.BitVec.extractLsb
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private theorem slliw_mul_eq_shift (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v * BitVec.ofNat 64 (2 ^ shamt.toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [extractLsb_mul_pow2]

abbrev slliw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev slliw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_muli_value v (BitVec.ofNat 64 (2 ^ shamt.toNat))) 31 0)

private theorem slliw_value_eq_sail (shamt : BitVec 5) (v : BitVec 64) :
    slliw_jolt_val shamt v = slliw_sail_operation shamt v := by
  simp only [slliw_jolt_val, slliw_sail_operation, jolt_virtual_muli_value]
  exact slliw_mul_eq_shift v shamt

theorem execute_SHIFTIWOP_SLLIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (slliw_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind, slliw_sail_operation]

/-- Program-level concrete theorem for `SLLIW`.

The Jolt-ISA program uses `VirtualMULI` with the immediate power of two, then
sign-extends the low word of `rd`. -/
theorem slliwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (slliw_sail_operation shamt v) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualMULI rd, rs1, 2^shamt` writes the shifted product to `rd`.
  let multiplier := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let shiftedProduct := jolt_virtual_muli_value v multiplier
  obtain ⟨js_afterMuli, h_muli_reads_rs1, h_muli_writes_shifted_product,
      h_muli_succeeds⟩ :=
    JoltISA.exists_jolt_state_after_virtual_muli_run_xreg_xreg rd rs1 multiplier js v hok
  have h_muli_writes_shifted_product' :
      js_afterMuli.sail = stateAfterWrite js.sail rd shiftedProduct := by
    simp only [shiftedProduct]
    exact h_muli_writes_shifted_product

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SLLIW result.
  let jolt_val := slliw_jolt_val shamt v
  obtain ⟨js_afterSignExtend, h_sign_extend_reads_shifted_product,
      h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
      rd rd js_afterMuli js.sail shiftedProduct hrd h_muli_writes_shifted_product'

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.slliwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMuli h_muli_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMuli js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, v, h_muli_reads_rs1, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLLIW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    rw [h_sign_extend_writes_jolt_val, h_muli_writes_shifted_product']
    change stateAfterWrite (stateAfterWrite js.sail rd shiftedProduct) rd jolt_val =
      stateAfterWrite js.sail rd jolt_val
    exact stateAfterWrite_stateAfterWrite rd shiftedProduct jolt_val js.sail

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SLLIW value.
  have h_slliw_value :
      jolt_val = slliw_sail_operation shamt v := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact slliw_value_eq_sail shamt v

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_slliw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SLLIW`. -/
theorem slliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run js.sail := by
  obtain ⟨js_afterSignExtend, v, h_read_rs1, h_program_succeeds, h_final_sail⟩ :=
    slliwProgram_concrete shamt rs1 rd hrd js hwf

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_SHIFTIWOP_SLLIW_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (slliw_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (slliw_sail_operation shamt v) js.sail s' h_write).symm

end
