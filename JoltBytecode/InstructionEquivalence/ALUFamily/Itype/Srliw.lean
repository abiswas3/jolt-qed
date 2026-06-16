import JoltBytecode.InstructionEquivalence.ALUFamily.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRLI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLIW: Jolt SLLI 32 + VirtualSRLI + VSEW = Sail SRLIW

Jolt program sequence:
1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `VirtualSRLI rd, v0, srliwBitmask shamt` — logical right shift by `ctz(bitmask)`
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The bitmask encodes `shamt + 32` via its count-trailing-zeros; see
`ctz_srliw_imm`.
-/

def srliw_imm (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat + 32
  let len := 64
  let ones := (1 <<< (len - shift)) - 1
  ones <<< shift

theorem ctz_srliw_imm (shamt : BitVec 64) :
    ctz (srliw_imm shamt) = (shamt.setWidth 5).toNat + 32 := by
  unfold srliw_imm
  simp only [Nat.shiftLeft_eq, one_mul]
  have h_lt : (shamt.setWidth 5).toNat < 32 := by
    have := (shamt.setWidth 5).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - ((shamt.setWidth 5).toNat + 32) := by omega
  have h_m_pos : 0 < 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) - 1 := by
    have : 2 ≤ 2 ^ (64 - ((shamt.setWidth 5).toNat + 32)) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 ((shamt.setWidth 5).toNat + 32) h_m_pos,
      ctz_of_odd (pow2_sub_one_odd h_diff_pos)]

private theorem setWidth_5_roundtrip (shamt : BitVec 5) :
    (shamt.setWidth 64).setWidth 5 = shamt := by
  ext i; simp

private theorem ctz_srliw_imm_shamt5 (shamt : BitVec 5) :
    ctz (srliw_imm (shamt.setWidth 64)) = shamt.toNat + 32 := by
  rw [ctz_srliw_imm, setWidth_5_roundtrip]

private theorem srliw_shift_eq (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [ctz_srliw_imm_shamt5]
  simp only [sign_extend, shift_bits_right, Sail.BitVec.signExtend,
             Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd]
  congr 1
  unfold BitVec.extractLsb'
  have nat_shr_zero : ∀ n : Nat, n >>> 0 = n := by simp
  simp only [nat_shr_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have h_shl : (v <<< 32).toNat = v.toNat * 2^32 % 2^64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hs : shamt.toNat < 32 := by have := shamt.isLt; norm_num at this; exact this
  have h_cancel : v.toNat * 2^32 % 2^64 / 2^(shamt.toNat + 32) = v.toNat % 2^32 / 2^shamt.toNat := by
    have h1 : v.toNat * 2^32 % 2^64 = v.toNat % 2^32 * 2^32 := by omega
    have h2 : (2:Nat)^(shamt.toNat + 32) = 2^shamt.toNat * 2^32 := by rw [Nat.pow_add]
    rw [h1, h2, Nat.mul_div_mul_right _ _ (by positivity : (0:Nat) < 2^32)]
  rw [h_shl, h_cancel]
  simp only [Nat.reducePow]
  have hbound : v.toNat % 4294967296 / 2 ^ shamt.toNat < 4294967296 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by positivity))
  rw [Nat.mod_eq_of_lt hbound]
  change _ = (BitVec.ofNat 32 v.toNat >>> (shamt).toNat).toNat
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]

private theorem srliwProgram_bitmask_eq (shamt : BitVec 5) :
    JoltISA.srliwBitmask shamt = srliw_imm (shamt.setWidth 64) := by
  unfold JoltISA.srliwBitmask srliw_imm
  rw [setWidth_5_roundtrip]

abbrev srliw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev srliw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srli_value (shift_bits_left v (32 : BitVec 6))
        (JoltISA.srliwBitmask shamt)) 31 0)

-- NOTE: Math theorem: the Jolt bitmask SRLIW sequence computes Sail SRLIW.
private theorem virtual_srliw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    srliw_jolt_val shamt v = srliw_sail_operation shamt v := by
  simp only [srliw_jolt_val, srliw_sail_operation]
  rw [srliwProgram_bitmask_eq]
  simpa only [jolt_virtual_srli_value, shift_bits_left] using srliw_shift_eq v shamt

theorem execute_SHIFTIWOP_SRLIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (srliw_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind, srliw_sail_operation]

/-- Program-level concrete theorem for `SRLIW`.

The program shifts `rs1` left into scratch `v0`, applies `VirtualSRLI` with the
encoded immediate bitmask, and then sign-extends `rd`. -/
theorem srliwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.srliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (srliw_sail_operation shamt v) := by

  -- Instruction 1: `SLLI v0, rs1, 32` writes the left-shifted source to `v0`.
  let leftShiftedSource := shift_bits_left v (32 : BitVec 6)
  obtain ⟨js_afterLeftShift, h_left_shift_reads_rs1, h_left_shift_keeps_sail,
      h_left_shift_writes_leftShiftedSource, _, h_left_shift_block_succeeds⟩ :=
    JoltISA.exists_state_after_slli_block_run_vreg_xreg
      JoltISA.inlineTmp0 rs1 (32 : BitVec 6) js v h_read_rs1

  -- Instruction 2: `VirtualSRLI rd, v0, srliwBitmask shamt` writes the shifted result.
  let bitmask := JoltISA.srliwBitmask shamt
  let shiftedResult := jolt_virtual_srli_value leftShiftedSource bitmask
  obtain ⟨js_afterSrli, h_srli_writes_shiftedResult, h_srli_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srli_run_xreg_vreg_of_value
      rd JoltISA.inlineTmp0 bitmask js_afterLeftShift js.sail leftShiftedSource
      h_left_shift_keeps_sail h_left_shift_writes_leftShiftedSource

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SRLIW result.
  let jolt_val := srliw_jolt_val shamt v
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterSrli js.sail shiftedResult h_srli_writes_shiftedResult

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.srliwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [h_left_shift_block_succeeds _]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLeftShift js_afterSrli
      h_srli_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrli js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRLIW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's three-instruction value is Sail's SRLIW value.
  have h_srliw_value :
      jolt_val = srliw_sail_operation shamt v := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_srliw_value_eq v shamt

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srliw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRLIW`. -/
theorem srliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (h : ALUFamily.UnarySourceReadAssumptions rs1 js) :
    ProgramMatchesSailWithProtectedFrame js
      ((JoltISA.execProgram (JoltISA.srliwProgram shamt rs1 rd)).run js)
      ((execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run js.sail) := by
  apply programMatchesSailWithProtectedFrame_of_projectResult_eq
  · let v := h.rs1_val
    have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      unfold JoltISA.srliwProgram
      rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [projectResult, project]
      rw [execute_SHIFTIWOP_SRLIW_factored shamt rs1 (regidx.Regidx 0)]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [h_read_rs1]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
      srliwProgram_concrete shamt rs1 rd js v h_read_rs1 hrd

    rw [h_program_succeeds]
    simp only [projectResult, project]
    rw [h_final_sail]

    rw [execute_SHIFTIWOP_SRLIW_factored shamt rs1 rd]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1]

    obtain ⟨s', h_write⟩ := wX_shape rd (srliw_sail_operation shamt v) js.sail
    simp only [h_write]
    congr 1
    exact (wX_bits_eq_stateAfterWrite rd (srliw_sail_operation shamt v) js.sail s' h_write).symm
  · unfold JoltISA.srliwProgram JoltISA.slliBlock
    apply JoltISA.pureWritebackTraceProgram_writesNoProtected
    simp [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg,
      JoltISA.DstWritesNoProtectedVReg]

end
