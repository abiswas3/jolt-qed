import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.ORI
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLW: SLLI + ORI + bitmask + VirtualSRL + VSEW = Sail SRLW

Jolt program sequence:
1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `ORI v1, rs2, 32` — set bit 5 of the shift amount
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask
4. `VirtualSRL rd, v0, v1` — logical right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that the `SLLI 32` plus encoded bitmask shift
agrees with Sail's word logical right shift.
  -/

abbrev srlw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev srlw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srl_value (shift_bits_left v1 (32 : BitVec 6))
        (jolt_virtual_shift_right_bitmask_value
          (v2 ||| sign_extend (m := 64) (32 : BitVec 12)))) 31 0)

theorem execute_RTYPEW_SRLW_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRLW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (srlw_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPEW]
  simp only [bind_pure_comp, pure_bind, srlw_sail_operation]

private def srlw_bitmask (rs2_val : BitVec 64) : Nat :=
  let v_bitmask_in := Riscv.ori rs2_val 32#64
  let shift := (v_bitmask_in.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

private theorem or32_setWidth6_toNat (x : BitVec 64) :
    ((Riscv.ori x 32#64).setWidth 6).toNat = (x.setWidth 5).toNat + 32 := by
  have h : (Riscv.ori x 32#64).setWidth 6 = ((1#1) +++ x.setWidth 5) := by
    unfold Riscv.ori
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp
    all_goals rw [BitVec.getElem_append]
    all_goals simp [BitVec.getElem_setWidth]
  rw [h, BitVec.toNat_append]
  norm_num [Nat.shiftLeft_eq]
  change (2 ^ 5 ||| (x.setWidth 5).toNat) = (x.setWidth 5).toNat + 32
  rw [show (x.setWidth 5).toNat + 32 = 2 ^ 5 + (x.setWidth 5).toNat by
    norm_num
    omega]
  have hx : (x.setWidth 5).toNat < 2 ^ 5 := by
    have := (x.setWidth 5).isLt
    norm_num at this
    exact this
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor]
  by_cases hi5 : i = 5
  · subst i
    rw [Nat.testBit_two_pow_self, Nat.testBit_two_pow_add_eq]
    have hk : (x.setWidth 5).toNat.testBit 5 = false := Nat.testBit_lt_two_pow hx
    simpa [BitVec.toNat_setWidth] using hk
  · by_cases hlt : i < 5
    · have hpow : (2 ^ 5 : Nat).testBit i = false := by
        rw [Nat.testBit_two_pow]
        simp [show ¬5 = i by omega]
      rw [hpow, Bool.false_or, Nat.testBit_two_pow_add_gt hlt]
    · have hgt : 5 < i := by omega
      have hk : (x.setWidth 5).toNat.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)))
      have hpow : (2 ^ 5 : Nat).testBit i = false := by
        rw [Nat.testBit_two_pow]
        simp [show ¬5 = i by omega]
      have hadd : (2 ^ 5 + (x.setWidth 5).toNat).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have hb : 2 ^ 5 + (x.setWidth 5).toNat < 2 ^ 6 := by omega
        exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
      rw [hpow, hk, hadd]
      rfl

private lemma ctz_srlw_bitmask (rs2_val : BitVec 64) :
    ctz (srlw_bitmask rs2_val) = (rs2_val.setWidth 5).toNat + 32 := by
  unfold srlw_bitmask
  simp only [or32_setWidth6_toNat]
  simp only [Nat.shiftLeft_eq, one_mul]
  have h_lt : (rs2_val.setWidth 5).toNat < 32 := by
    have := (rs2_val.setWidth 5).isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - ((rs2_val.setWidth 5).toNat + 32) := by omega
  have h_m_pos : 0 < 2 ^ (64 - ((rs2_val.setWidth 5).toNat + 32)) - 1 := by
    have : 2 ≤ 2 ^ (64 - ((rs2_val.setWidth 5).toNat + 32)) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 ((rs2_val.setWidth 5).toNat + 32) h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]

private lemma toNat_shl_32 (v : BitVec 64) :
    (v <<< 32).toNat = v.toNat * 2^32 % 2^64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

private lemma mul_mod_div_cancel (a s : Nat) (hs : s < 32) :
    a * 2^32 % 2^64 / 2^(s + 32) = a % 2^32 / 2^s := by
  have h1 : a * 2^32 % 2^64 = a % 2^32 * 2^32 := by omega
  have h2 : (2:Nat)^(s + 32) = 2^s * 2^32 := by
    have : (2:Nat)^32 = 2^32 := rfl
    rw [Nat.pow_add]
  rw [h1, h2, Nat.mul_div_mul_right _ _ (by positivity : (0:Nat) < 2^32)]

private lemma nat_shr_zero (n : Nat) : n >>> 0 = n := by simp

private lemma shl_shr_setWidth (v1 v2 : BitVec 64)
    (hs : (v2.setWidth 5).toNat < 32) :
    BitVec.extractLsb' 0 32 (v1 <<< 32 >>> ((v2.setWidth 5).toNat + 32)) =
    BitVec.extractLsb' 0 32 v1 >>> BitVec.extractLsb' 0 5 (BitVec.extractLsb' 0 32 v2) := by
  unfold BitVec.extractLsb'
  simp only [nat_shr_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             Nat.reducePow]
  rw [toNat_shl_32 v1, mul_mod_div_cancel v1.toNat _ hs]
  simp only [Nat.reducePow]
  have hbound : v1.toNat % 4294967296 / 2 ^ (BitVec.setWidth 5 v2).toNat < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
  rw [Nat.mod_eq_of_lt hbound]
  change _ = (BitVec.ofNat 32 v1.toNat >>> (BitVec.ofNat 5 (v2.toNat % 4294967296)).toNat).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have : v2.toNat % 4294967296 % 32 = (BitVec.setWidth 5 v2).toNat := by
    simp [BitVec.toNat_setWidth]
  rw [this]

private theorem srlw_shift_eq (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v1 <<< 32) >>> ctz (srlw_bitmask v2)) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [show ctz (srlw_bitmask v2) = (v2.setWidth 5).toNat + 32 from ctz_srlw_bitmask v2]
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend,
             Sail.BitVec.extractLsb, BitVec.extractLsb,
             Nat.sub_zero, Nat.reduceAdd]
  congr 1
  have hs : (v2.setWidth 5).toNat < 32 := by
    have := (v2.setWidth 5).isLt; norm_num at this; exact this
  exact shl_shr_setWidth v1 v2 hs

-- NOTE: Math theorem: the Jolt bitmask SRL sequence computes Sail SRLW.
private lemma virtual_srlw_value_eq
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    srlw_jolt_val v1 v2 = srlw_sail_operation v1 v2 := by
  simp only [srlw_jolt_val, srlw_sail_operation]
  rw [← srlw_shift_eq v1 v2]
  unfold jolt_virtual_srl_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value, ctz_srlw_bitmask]
  have hsign : sign_extend (m := 64) (32 : BitVec 12) = (32#64) := by decide
  have hmask :
      ((v2 ||| sign_extend (m := 64) (32 : BitVec 12)).setWidth 6).toNat =
        (v2.setWidth 5).toNat + 32 := by
    rw [hsign]
    simpa only [Riscv.ori] using (or32_setWidth6_toNat v2)
  rw [hmask]
  simp only [shift_bits_left]
  rfl

private theorem inlineTmp0_ne_inlineTmp1 : JoltISA.inlineTmp1 ≠ JoltISA.inlineTmp0 := by
  decide

/-- Program-level concrete theorem for `SRLW`.

The program theorem follows the five Rust-emitted steps: shift `rs1` left into
scratch `v0`, set bit five of `rs2` in scratch `v1`, encode that as a virtual
right-shift bitmask, run `VirtualSRL`, and finally sign-extend `rd`. -/
theorem srlwProgram_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (srlw_sail_operation v1 v2) := by
  -- Instruction 1: `SLLI v0, rs1, 32` writes the left-shifted source to `v0`.
  let leftShiftedSource := shift_bits_left v1 (32 : BitVec 6)
  obtain ⟨js_afterLeftShift, h_left_shift_reads_rs1, h_left_shift_keeps_sail,
      h_left_shift_writes_leftShiftedSource, _, h_left_shift_block_succeeds⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_xreg
      JoltISA.inlineTmp1 rs1 (32 : BitVec 6) js v1 h_read_rs1
      (by unfold WritableVReg; decide)

  -- Instruction 2: `ORI v1, rs2, 32` writes the encoded shift amount to `v1`.
  let encodedShift := v2 ||| sign_extend (m := 64) (32 : BitVec 12)
  obtain ⟨js_afterOri, h_ori_reads_rs2, h_ori_keeps_sail,
      h_ori_writes_encodedShift, h_ori_preserves_leftShiftedSource, h_ori_succeeds⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_preserving_value
      JoltISA.inlineTmp0 JoltISA.inlineTmp1 rs2 (32 : BitVec 12)
      js_afterLeftShift js.sail v2 leftShiftedSource
      h_left_shift_keeps_sail h_read_rs2 h_left_shift_writes_leftShiftedSource
      inlineTmp0_ne_inlineTmp1
      (by unfold WritableVReg; decide)

  -- Instruction 3: `VirtualShiftRightBitmask v1, v1` writes the shift bitmask to `v1`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value encodedShift
  obtain ⟨js_afterBitmask, h_bitmask_keeps_sail, h_bitmask_writes_shiftBitmask,
      h_bitmask_preserves_leftShiftedSource, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_vreg_preserving_value
      JoltISA.inlineTmp0 JoltISA.inlineTmp0 JoltISA.inlineTmp1
      js_afterOri js.sail encodedShift leftShiftedSource
      h_ori_keeps_sail h_ori_writes_encodedShift h_ori_preserves_leftShiftedSource
      inlineTmp0_ne_inlineTmp1
      (by unfold WritableVReg; decide)

  -- Instruction 4: `VirtualSRL rd, v0, v1` writes the shifted result to `rd`.
  let shiftedResult := jolt_virtual_srl_value leftShiftedSource shiftBitmask
  obtain ⟨js_afterSrl, h_srl_writes_shiftedResult, h_srl_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_vreg_vreg_of_values
      rd JoltISA.inlineTmp1 JoltISA.inlineTmp0 js_afterBitmask js.sail
      leftShiftedSource shiftBitmask h_bitmask_keeps_sail
      h_bitmask_preserves_leftShiftedSource h_bitmask_writes_shiftBitmask

  -- Instruction 5: `VirtualSignExtendWord rd, rd` writes the SRLW result.
  let jolt_val := srlw_jolt_val v1 v2
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterSrl js.sail shiftedResult h_srl_writes_shiftedResult

  -- Full program succeeds by stepping through the five instruction runs.
  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.srlwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [h_left_shift_block_succeeds _]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLeftShift js_afterOri h_ori_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterOri js_afterBitmask
      h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSrl
      h_srl_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrl js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRLW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's five-instruction value is Sail's SRLW value.
  have h_srlw_value :
      jolt_val = srlw_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_srlw_value_eq v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srlw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRLW`. -/
def srlwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) : Prop :=
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.srlwProgram rs2 rs1 rd)).run js)
      ((execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail)

/-- Main program-level equivalence for `SRLW`. -/
theorem srlwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : ALUFamily.BinarySourceReadAssumptions rs2 rs1 js) :
    srlwProgramEqSailStatement rs2 rs1 rd js h := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · let v1 := h.rs1_val
    let v2 := h.rs2_val
    have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
    have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      unfold JoltISA.srlwProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [projectResult, project]
      rw [execute_RTYPEW_SRLW_factored rs2 rs1 (regidx.Regidx 0)]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [h_read_rs1, h_read_rs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
      srlwProgram_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd

    -- Use the concrete proof to collapse the Jolt side to its final Sail state.
    rw [h_program_succeeds]
    simp only [projectResult, project]
    rw [h_final_sail]

    -- Expand the Sail-side `SRLW`: it reads the same inputs and writes the same
    -- already-proved final value.
    rw [execute_RTYPEW_SRLW_factored rs2 rs1 rd]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]

    -- The only remaining mismatch is the concrete state chosen by `wX_bits`
    -- versus our `stateAfterWrite` spelling of that same register update.
    obtain ⟨s', h_write⟩ := wX_shape rd (srlw_sail_operation v1 v2) js.sail
    simp only [h_write]
    congr 1
    exact (wX_bits_eq_stateAfterWrite rd (srlw_sail_operation v1 v2) js.sail s' h_write).symm
  · unfold JoltISA.srlwProgram JoltISA.slliBlock
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]

end
