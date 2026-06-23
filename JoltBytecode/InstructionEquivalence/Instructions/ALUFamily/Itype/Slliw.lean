import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualMULI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

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
theorem slliwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (slliw_sail_operation shamt v) := by

  -- Instruction 1: `VirtualMULI rd, rs1, 2^shamt` writes the shifted product to `rd`.
  let multiplier := BitVec.ofNat 64 (2 ^ shamt.toNat)
  let shiftedProduct := jolt_virtual_muli_value v multiplier
  obtain ⟨js_afterMuli, h_muli_reads_rs1, h_muli_writes_shiftedProduct,
      h_muli_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_muli_run_xreg_xreg rd rs1 multiplier js v h_read_rs1

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the SLLIW result.
  let jolt_val := slliw_jolt_val shamt v
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterMuli js.sail shiftedProduct h_muli_writes_shiftedProduct

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.slliwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMuli h_muli_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMuli js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLLIW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

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

/-- `SLLIW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem slliwProgram_preserves_projected_vregs
    (shamt : BitVec 5) (rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.slliwProgram shamt rs1 rd) := by
    unfold JoltISA.slliwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg,
      true_and]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `SLLIW`. -/
def slliwProgramEqSailStatement (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.slliwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW).run js.sail

/-- Main program-level equivalence for `SLLIW`. -/
theorem slliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    slliwProgramEqSailStatement shamt rs1 rd js h := by
  unfold slliwProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.slliwProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_SHIFTIWOP_SLLIW_factored shamt rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    slliwProgram_concrete shamt rs1 rd js v h_read_rs1 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSignExtend :=
    slliwProgram_preserves_projected_vregs shamt rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_SHIFTIWOP_SLLIW_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (slliw_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSignExtend rd (slliw_sail_operation shamt v)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (slliw_sail_operation shamt v)
    js.sail s' h_write).symm

end
