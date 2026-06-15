import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.ANDI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRA
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAW: 5-step bitmask-encoded arithmetic right shift = Sail SRAW

Jolt program sequence:
1. `VirtualSignExtendWord v0, rs1` — sign-extend `rs1[31:0]` to 64 bits
2. `ANDI v1, rs2, 0x1f` — mask shift amount to 5 bits
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask from `v1`
4. `VirtualSRA rd, v0, v1` — arithmetic right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that sign-extending the source word, masking
the shift amount, and using the virtual arithmetic shift agrees with Sail's
word arithmetic right shift.
  -/

abbrev sraw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sraw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_sra_value
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
        (jolt_virtual_shift_right_bitmask_value
          (v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)))) 31 0)

theorem execute_RTYPEW_SRAW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sraw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, sraw_sail_operation]

private theorem and31_setWidth6_toNat (rs2_val : BitVec 64) :
    ((Riscv.andi rs2_val 0x1f#64).setWidth 6).toNat = (rs2_val.setWidth 5).toNat := by
  unfold Riscv.andi
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : (31 : Nat) % 2 ^ 64 = 31 := by norm_num
  rw [h1, show (31 : Nat) = 2 ^ 5 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by
    have := Nat.mod_lt rs2_val.toNat (show 0 < 2 ^ 5 from by positivity)
    omega)

private lemma sail_sraw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sraw v1 v2 := by
  unfold Riscv.sraw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']
  congr 2

private lemma signExtend64_sshiftRight_setWidth32 (x : BitVec 32) (s : Nat)
    (hs : s < 32) :
    ((x.signExtend 64).sshiftRight s).setWidth 32 = x.sshiftRight s := by
  ext i hi
  simp only [BitVec.getElem_setWidth]
  rw [BitVec.getLsbD_sshiftRight, BitVec.getElem_sshiftRight]
  have hi64 : ¬64 ≤ i := by omega
  have hi32 : ¬32 ≤ i := by omega
  have hshift64 : s + i < 64 := by omega
  by_cases hshift32 : s + i < 32
  · simp [hi64, hshift64, hshift32, ← BitVec.getLsbD_eq_getElem,
      BitVec.getLsbD_signExtend]
  · simp [hi64, hshift64, hshift32, BitVec.getLsbD_signExtend,
      -BitVec.getLsbD_eq_getElem, BitVec.msb_eq_getLsbD_last]

private theorem sraw_virtual_sra_value (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)).sshiftRight
          (v2.setWidth 5).toNat) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [sail_sraw_eq_riscv]
  unfold Riscv.sraw sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.extractLsb']
  exact congrArg (fun x : BitVec 32 => x.signExtend 64)
    (signExtend64_sshiftRight_setWidth32 (v1.setWidth 32) (v2.toNat % 32) (by omega))

-- NOTE: Math theorem: the Jolt bitmask SRA sequence computes Sail SRAW.
private lemma virtual_sraw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    sraw_jolt_val v1 v2 = sraw_sail_operation v1 v2 := by
  simp only [sraw_jolt_val, sraw_sail_operation]
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  have hsign : sign_extend (m := 64) (0x1f : BitVec 12) = (0x1f#64) := by decide
  have hmask :
      ((v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat := by
    rw [hsign]
    simpa only [Riscv.andi] using (and31_setWidth6_toNat v2)
  rw [hmask]
  exact sraw_virtual_sra_value v1 v2

private theorem inlineTmp0_ne_inlineTmp1 : JoltISA.inlineTmp0 ≠ JoltISA.inlineTmp1 := by
  decide

/-- Program-level concrete theorem for `SRAW`.

This follows the five emitted steps: sign-extend `rs1[31:0]` into scratch
`v0`, mask `rs2` into scratch `v1`, encode `v1` as a right-shift bitmask, run
`VirtualSRA`, then sign-extend `rd` once more. -/
theorem srawProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (sraw_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualSignExtendWord v0, rs1` writes the signed source word to `v0`.
  let signedSource := sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0)
  obtain ⟨js_afterSourceSignExtend, h_source_sign_extend_reads_rs1,
      h_source_sign_extend_keeps_sail, h_source_sign_extend_writes_signedSource,
      _, h_source_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_vreg_xreg
      JoltISA.inlineTmp0 rs1 js v1 h_read_rs1

  -- Instruction 2: `ANDI v1, rs2, 0x1f` writes the masked shift amount to `v1`.
  let maskedShift := v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)
  obtain ⟨js_afterAndi, h_andi_reads_rs2, h_andi_keeps_sail,
      h_andi_writes_maskedShift, h_andi_preserves_signedSource, h_andi_succeeds⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_preserving_value
      JoltISA.inlineTmp1 JoltISA.inlineTmp0 rs2 (0x1f : BitVec 12)
      js_afterSourceSignExtend js.sail v2 signedSource
      h_source_sign_extend_keeps_sail h_read_rs2 h_source_sign_extend_writes_signedSource
      inlineTmp0_ne_inlineTmp1

  -- Instruction 3: `VirtualShiftRightBitmask v1, v1` writes the shift bitmask to `v1`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value maskedShift
  obtain ⟨js_afterBitmask, h_bitmask_keeps_sail, h_bitmask_writes_shiftBitmask,
      h_bitmask_preserves_signedSource, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_vreg_preserving_value
      JoltISA.inlineTmp1 JoltISA.inlineTmp1 JoltISA.inlineTmp0
      js_afterAndi js.sail maskedShift signedSource
      h_andi_keeps_sail h_andi_writes_maskedShift h_andi_preserves_signedSource
      inlineTmp0_ne_inlineTmp1

  -- Instruction 4: `VirtualSRA rd, v0, v1` writes the shifted result to `rd`.
  let shiftedResult := jolt_virtual_sra_value signedSource shiftBitmask
  obtain ⟨js_afterSra, h_sra_writes_shiftedResult, h_sra_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sra_run_xreg_vreg_vreg_of_values
      rd JoltISA.inlineTmp0 JoltISA.inlineTmp1 js_afterBitmask js.sail
      signedSource shiftBitmask h_bitmask_keeps_sail
      h_bitmask_preserves_signedSource h_bitmask_writes_shiftBitmask

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRAW result.
  let jolt_val := sraw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterSra js.sail shiftedResult h_sra_writes_shiftedResult

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.srawProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSourceSignExtend
      h_source_sign_extend_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSourceSignExtend js_afterAndi
      h_andi_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterAndi js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSra
      h_sra_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSra js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRAW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's five-instruction value is Sail's SRAW value.
  have h_sraw_value :
      jolt_val = sraw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_sraw_value_eq v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sraw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRAW`. -/
theorem srawProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    projectResult ((JoltISA.execProgram (JoltISA.srawProgram rs2 rs1 rd)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail := by
  let v1 := h.rs1_val
  let v2 := h.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read.value_eq
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read.value_eq
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srawProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_RTYPEW_SRAW_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    srawProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

  -- Use the concrete proof to collapse the Jolt side to its final Sail state.
  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  -- Expand the Sail-side `SRAW`: it reads the same inputs and writes the same
  -- already-proved final value.
  rw [execute_RTYPEW_SRAW_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  -- The only remaining mismatch is the concrete state chosen by `wX_bits`
  -- versus our `stateAfterWrite` spelling of that same register update.
  obtain ⟨s', h_write⟩ := wX_shape rd (sraw_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sraw_sail_operation v1 v2) js.sail s' h_write).symm

end
