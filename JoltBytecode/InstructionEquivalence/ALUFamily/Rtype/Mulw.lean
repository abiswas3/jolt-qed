import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.StraightLine
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
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sail_operation v1 v2) := by
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2

  -- Instruction 1: `MUL rd, rs1, rs2` writes the 64-bit product to `rd`.
  let product := v1 * v2
  obtain ⟨js_afterMul, h_mul_reads_rs1, h_mul_reads_rs2,
      h_mul_writes_product, h_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_xreg rd rs1 rs2 js v1 v2 hok1 hok2

  -- Instruction 2: `VirtualSignExtendWord rd, rd` writes the MULW result.
  let mulwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb product 31 0)
  obtain ⟨js_afterSignExtend, h_sign_extend_reads_product, h_sign_extend_writes_result,
      h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_source_write
      rd rd js_afterMul js.sail product hrd h_mul_writes_product

  -- Full program succeeds by stepping through the two instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.mulwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, v1, v2, h_mul_reads_rs1, h_mul_reads_rs2,
    h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt MULW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd mulwResult := by
    rw [h_sign_extend_writes_result, h_mul_writes_product]
    exact stateAfterWrite_stateAfterWrite rd product mulwResult js.sail

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

/-- Main program-level equivalence for `MULW`. -/
theorem mulwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState)
    (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.mulwProgram rs2 rs1 rd)).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail := by
  obtain ⟨js_afterSignExtend, v1, v2, h_read_rs1, h_read_rs2,
      h_program_succeeds, h_final_sail⟩ :=
    mulwProgram_concrete rs2 rs1 rd hrd js hwf

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `MULW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_MULW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sail_operation v1 v2) js.sail s' h_write).symm

end
