import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import Mathlib

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULW: Jolt MUL + VirtualSignExtendWord = Sail MULW

Jolt program sequence:
1. `MUL rd, rs1, rs2` — 64-bit multiply, writes `v1 * v2` to `rd`
2. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

Sail's `MULW` is a standalone function `execute_MULW` rather than a branch
of `execute_RTYPEW`. The uniform R-type W closer still applies because the
surface shape is the same: read `rs1`, read `rs2`, write `rd`, return.

The local value lemmas connect the Sail `to_bits_truncate ∘ toInt` idiom to
plain 32-bit `BitVec` multiply, and show truncation distributes over multiply.
-/

abbrev sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (to_bits_truncate (l := 32)
      (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
       BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))

theorem execute_MULW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_MULW]
  simp only [bind_pure_comp, pure_bind, sail_operation]

private theorem mod33_toNat_mod32 (x : Int) :
    (x % 8589934592).toNat % 4294967296 = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32 x

private theorem intCast_mul_toInt_32 (a b : BitVec 32) :
    (((BitVec.toInt a *i BitVec.toInt b : Int) : BitVec 32)) = a * b := by
  change BitVec.ofInt 32 (a.toInt * b.toInt) = a * b
  rw [BitVec.ofInt_mul]
  have h1 : BitVec.ofInt 32 a.toInt = a := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  have h2 : BitVec.ofInt 32 b.toInt = b := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  rw [h1, h2]

private theorem mulw32_eq_mul (a b : BitVec 32) :
    to_bits_truncate (l := 32) (BitVec.toInt a *i BitVec.toInt b) = a * b := by
  rw [trunc32_eq_intCast]
  exact intCast_mul_toInt_32 a b

/-- `(a * b)[31:0] = a[31:0] * b[31:0]`. -/
private theorem extractLsb_mul (v1 v2 : BitVec 64) :
    Sail.BitVec.extractLsb (v1 * v2) 31 0 =
      Sail.BitVec.extractLsb v1 31 0 * Sail.BitVec.extractLsb v2 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

/-- Math bridge: the Jolt value `g(f(v1, v2))` equals the Sail MULW value
`h(v1, v2)`. -/
private theorem mulw_value_eq_sail (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 * v2) 31 0) =
      sail_operation v1 v2 := by
  simp only [sail_operation]
  congr 1
  rw [extractLsb_mul, ← mulw32_eq_mul]

/-- Program-level concrete theorem for `MULW`.

The Jolt-ISA program records the inline sequence as ordinary 64-bit multiply
followed by sign-extension of the low word.  The pure bridge at the end
identifies that low-word multiply with Sail's signed 32-bit multiplication
encoding. -/
theorem mulwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sail_operation v1 v2) := by
  -- Instruction 1: `MUL rd, rs1, rs2` writes the 64-bit product to `rd`.
  let product := v1 * v2
  obtain ⟨js_afterMul, h_mul_reads_rs1, h_mul_reads_rs2,
      h_mul_writes_product, h_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 h_read_rs1 h_read_rs2

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the MULW result.
  let mulwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb product 31 0)
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_result,
      h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterMul js.sail product h_mul_writes_product

  -- Full program succeeds by stepping through the two instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.mulwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt MULW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd mulwResult := by
    exact h_sign_extend_writes_result

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's MULW value.
  have h_mulw_value :
      mulwResult = sail_operation v1 v2 := by
    simp only [mulwResult, product]
    -- NOTE: The core math theorem.
    exact mulw_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is just the same write
  -- with the value rewritten from the Sail spelling back to the Jolt spelling.
  rw [← h_mulw_value]
  exact h_final_jolt_value

/-- Rust's MULW `rd = x0` replacement retires successfully without changing
Jolt state. -/
private theorem mulw_rd_zero_noop_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (js : SailJoltState) :
    (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 (regidx.Regidx 0))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold JoltISA.mulwProgram
  rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
  exact JoltISA.pureWritebackRdZeroProgram_run js

/-- `MULW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem mulwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.mulwProgram rs2 rs1 rd) := by
    unfold JoltISA.mulwProgram
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `MULW`. -/
def mulwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail

/-- Main program-level equivalence for `MULW`. -/
theorem mulwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    mulwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold mulwProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    rw [mulw_rd_zero_noop_concrete rs2 rs1 js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_MULW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    mulwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSignExtend :=
    mulwProgram_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_MULW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSignExtend rd (sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (sail_operation v1 v2)
    js.sail s' h_write).symm

end
