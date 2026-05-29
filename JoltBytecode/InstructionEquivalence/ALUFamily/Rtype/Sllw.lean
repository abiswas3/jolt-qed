import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualPow2W
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLW: VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt program sequence:
1. `VirtualPow2W v0, rs2` — compute `2 ^ (rs2[4:0])`
2. `MUL rd, rs1, v0` — multiply `rs1` by the power of two
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that multiplying by `2 ^ rs2[4:0]` and then
sign-extending the low word agrees with Sail's word left shift.
  -/

abbrev sllw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sllw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v1 * jolt_virtual_pow2w_value v2) 31 0)

theorem execute_RTYPEW_SLLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SLLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sllw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, sllw_sail_operation]

private def sllwJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_pow := Jolt.virtualPow2W rs2_val
  let product := Riscv.mul rs1_val v_pow
  Jolt.virtualSignExtendWord product

private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth, Nat.shiftLeft_eq]

private theorem sllw_eq_sllwJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sllw rs1_val rs2_val = sllwJolt rs1_val rs2_val := by
  unfold Riscv.sllw sllwJolt Jolt.virtualPow2W Riscv.mul Jolt.virtualSignExtendWord
  congr 1
  exact sll_32_eq_mul_trunc rs1_val (rs2_val.setWidth 5).toNat (by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this)

private lemma mul_eq_sllwJolt (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sllwJolt v1 v2 := by
  unfold sllwJolt Jolt.virtualSignExtendWord Jolt.virtualPow2W Riscv.mul sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.extractLsb']
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]

private lemma sail_sllw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sllw v1 v2 := by
  unfold Riscv.sllw sign_extend shift_bits_left
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

private theorem sllw_mul_eq_shift (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)) 31 0) =
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [mul_eq_sllwJolt, sail_sllw_eq_riscv, sllw_eq_sllwJolt]

/-- Math bridge: the three-step Jolt SLLW value equals Sail's SLLW value. -/
private theorem sllw_value_eq_sail (v1 v2 : BitVec 64) :
    sllw_jolt_val v1 v2 = sllw_sail_operation v1 v2 := by
  simp only [sllw_jolt_val, sllw_sail_operation]
  unfold jolt_virtual_pow2w_value
  rw [sllw_mul_eq_shift v1 v2]

/-- Program-level concrete theorem for `SLLW`.

The expansion is `VirtualPow2W` into scratch `v0`, a real-destination
multiply by that scratch value, then `VirtualSignExtendWord` on `rd`. -/
theorem sllwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (sllw_sail_operation v1 v2) := by

  -- Instruction 1: `VirtualPow2W v0, rs2` writes `2 ^ rs2[4:0]` to `v0`.
  let pow2 := jolt_virtual_pow2w_value v2
  obtain ⟨js_afterPow2, h_pow2_reads_rs2, h_pow2_keeps_sail,
      h_pow2_writes_pow2, _, h_pow2_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_pow2w_run_vreg_xreg
      JoltISA.inlineTmp0 rs2 js v2 h_read_rs2

  -- Instruction 2: `MUL rd, rs1, v0` writes the shifted word product to `rd`.
  let product := v1 * pow2
  obtain ⟨js_afterMul, h_mul_reads_rs1, h_mul_writes_product, h_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_vreg_of_value
      rd rs1 JoltISA.inlineTmp0 js_afterPow2 js.sail v1 pow2
      h_pow2_keeps_sail h_read_rs1 h_pow2_writes_pow2

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SLLW result.
  let jolt_val := sllw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterMul js.sail product h_mul_writes_product

  -- Full program succeeds by stepping through the three instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.sllwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterPow2 h_pow2_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterPow2 js_afterMul h_mul_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterMul js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLLW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's three-instruction value is Sail's SLLW value.
  have h_sllw_value :
      jolt_val = sllw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact sllw_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sllw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.sllwProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sllwProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_RTYPEW_SLLW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    sllwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SLLW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SLLW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (sllw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sllw_sail_operation v1 v2) js.sail s' h_write).symm

end
