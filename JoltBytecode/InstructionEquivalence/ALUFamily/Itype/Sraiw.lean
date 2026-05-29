import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRAI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.JoltISA.Semantics.Instructions
import JoltBytecode.JoltISA.Values.Shift
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAIW: Jolt 3-step decomposition = Sail SRAIW

Jolt program sequence:
1. `VirtualSignExtendWord v1, rs1` — sign-extend `rs1[31:0]` to 64 bits
2. `VirtualSRAI rd, v1, sraiwBitmask shamt` — arithmetic right shift by `ctz(bitmask)`
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`
-/

def sraiw_bitmask (shamt : BitVec 64) : Nat :=
  let shift := (shamt.setWidth 5).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_sraiw_bitmask (shamt : BitVec 64) :
    ctz (sraiw_bitmask shamt) = (shamt.setWidth 5).toNat := by
  unfold sraiw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt.setWidth 5).toNat
  have h_lt : shift < 32 := by have := (shamt.setWidth 5).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private theorem setWidth_5_roundtrip (shamt : BitVec 5) :
    (shamt.setWidth 64).setWidth 5 = shamt := by
  ext i
  simp

private theorem extract_shamt64_low5 (shamt : BitVec 5) :
    Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (shamt.setWidth 64) 31 0) 4 0 = shamt := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_setWidth]
  exact shamt.isLt

private theorem sraiwProgram_bitmask_eq (shamt : BitVec 5) :
    JoltISA.sraiwBitmask shamt = sraiw_bitmask (shamt.setWidth 64) := by
  unfold JoltISA.sraiwBitmask sraiw_bitmask
  rw [setWidth_5_roundtrip]

abbrev sraiw_sail_operation (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)

abbrev sraiw_jolt_val (shamt : BitVec 5) (v : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srai_value
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
        (JoltISA.sraiwBitmask shamt)) 31 0)

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

-- NOTE: Math theorem: the Jolt bitmask SRAIW sequence computes Sail SRAIW.
private theorem virtual_sraiw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    sraiw_jolt_val shamt v = sraiw_sail_operation shamt v := by
  simp only [sraiw_jolt_val, sraiw_sail_operation]
  unfold jolt_virtual_srai_value
  rw [sraiwProgram_bitmask_eq, ctz_sraiw_bitmask, setWidth_5_roundtrip]
  simpa only [setWidth_5_roundtrip, extract_shamt64_low5] using
    sraw_virtual_sra_value v (shamt.setWidth 64)

theorem execute_SHIFTIWOP_SRAIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sraiw_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, sraiw_sail_operation]

/-- Program-level concrete theorem for `SRAIW`.

The program first sign-extends the source word into scratch `v1`, then runs
`VirtualSRAI` with the immediate bitmask, and finally sign-extends `rd`. -/
theorem sraiwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (sraiw_sail_operation shamt v) := by

  -- Instruction 1: `VirtualSignExtendWord v1, rs1` writes the signed source word to `v1`.
  let signedSource := sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)
  obtain ⟨js_afterSourceSignExtend, h_source_sign_extend_reads_rs1,
      h_source_sign_extend_keeps_sail, h_source_sign_extend_writes_signedSource,
      _, h_source_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_vreg_xreg
      (1 : JoltISA.VReg) rs1 js v h_read_rs1

  -- Instruction 2: `VirtualSRAI rd, v1, sraiwBitmask shamt` writes the shifted result.
  let bitmask := JoltISA.sraiwBitmask shamt
  let shiftedResult := jolt_virtual_srai_value signedSource bitmask
  obtain ⟨js_afterSrai, h_srai_writes_shiftedResult, h_srai_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srai_run_xreg_vreg_of_value
      rd (1 : JoltISA.VReg) bitmask js_afterSourceSignExtend js.sail signedSource
      h_source_sign_extend_keeps_sail h_source_sign_extend_writes_signedSource

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SRAIW result.
  let jolt_val := sraiw_jolt_val shamt v
  obtain ⟨js_afterSignExtend, h_sign_extend_writes_jolt_val, h_sign_extend_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg_of_same_register_write
      rd js_afterSrai js.sail shiftedResult h_srai_writes_shiftedResult

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js_afterSignExtend := by
    unfold JoltISA.sraiwProgram
    rw [JoltISA.pureWritebackTraceProgram_of_ne_zero hrd]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSourceSignExtend
      h_source_sign_extend_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSourceSignExtend js_afterSrai
      h_srai_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrai js_afterSignExtend
      h_sign_extend_succeeds]
    rfl

  refine ⟨js_afterSignExtend, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRAIW value.
  have h_final_jolt_value :
      js_afterSignExtend.sail = stateAfterWrite js.sail rd jolt_val := by
    exact h_sign_extend_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's three-instruction value is Sail's SRAIW value.
  have h_sraiw_value :
      jolt_val = sraiw_sail_operation shamt v := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact virtual_sraiw_value_eq v shamt

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sraiw_value]
  exact h_final_jolt_value

/-- Main program-level equivalence for `SRAIW`. -/
theorem sraiwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx) (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail) :
    projectResult ((JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run js.sail := by
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sraiwProgram
    rw [JoltISA.pureWritebackTraceProgram_regidx_zero]
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [projectResult, project]
    rw [execute_SHIFTIWOP_SRAIW_factored shamt rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSignExtend, h_program_succeeds, h_final_sail⟩ :=
    sraiwProgram_concrete shamt rs1 rd js v h_read_rs1 hrd

  rw [h_program_succeeds]
  simp only [projectResult, project]
  rw [h_final_sail]

  rw [execute_SHIFTIWOP_SRAIW_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (sraiw_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd (sraiw_sail_operation shamt v) js.sail s' h_write).symm

end
