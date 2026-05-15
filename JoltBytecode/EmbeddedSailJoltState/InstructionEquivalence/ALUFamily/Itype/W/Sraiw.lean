import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Shift
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSRAI
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Instructions.VirtualSignExtendWord
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

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

-- NOTE: Math theorem: the Jolt bitmask SRAIW sequence computes Sail SRAIW.
private theorem virtual_sraiw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (jolt_virtual_srai_value
          (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
          (JoltISA.sraiwBitmask shamt)) 31 0) =
    sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
  unfold jolt_virtual_srai_value
  rw [sraiwProgram_bitmask_eq, ctz_sraiw_bitmask, setWidth_5_roundtrip]
  simpa only [setWidth_5_roundtrip, extract_shamt64_low5] using
    sraw_virtual_sra_value v (shamt.setWidth 64)

theorem execute_SHIFTIWOP_SRAIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64)
        (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

/-- Program-level concrete theorem for `SRAIW`.

The program first sign-extends the source word into scratch `v1`, then runs
`VirtualSRAI` with the immediate bitmask, and finally sign-extends `rd`. -/
theorem sraiwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  obtain ⟨v, hok⟩ := hwf rs1

  -- Instruction 1: `VirtualSignExtendWord v1, rs1` writes the signed source word to `v1`.
  let signedSource := sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)
  let js_afterSourceSignExtend : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then signedSource else js.vregs r }
  have h_source_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg 1) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js_afterSourceSignExtend := by
    simpa only [js_afterSourceSignExtend, signedSource] using
      (JoltISA.virtual_sign_extend_word_run_vreg_xreg (1 : JoltISA.VReg) rs1 js v hok)

  -- Instruction 2: `VirtualSRAI rd, v1, sraiwBitmask shamt` writes the shifted result.
  let bitmask := JoltISA.sraiwBitmask shamt
  let shiftedResult := jolt_virtual_srai_value signedSource bitmask
  obtain ⟨s_afterSrai, h_virtual_srai_run, h_virtual_srai_write⟩ :=
    JoltISA.exists_state_after_virtual_srai_run_xreg_vreg rd (1 : JoltISA.VReg)
      bitmask js_afterSourceSignExtend
  have h_srai_writes_shifted_result :
      wX_bits rd shiftedResult js.sail = .ok () s_afterSrai := by
    simpa only [js_afterSourceSignExtend, shiftedResult, signedSource, bitmask] using
      h_virtual_srai_write
  let js_afterSrai : SailJoltState :=
    { sail := s_afterSrai, vregs := js_afterSourceSignExtend.vregs }
  have h_sail_after_srai :
      js_afterSrai.sail = stateAfterWrite js.sail rd shiftedResult := by
    simpa only [js_afterSrai, shiftedResult] using
      wX_bits_eq_stateAfterWrite rd shiftedResult js.sail s_afterSrai
        h_srai_writes_shifted_result
  have h_virtual_srai_succeeds :
      (JoltISA.execInstr (.VirtualSRAI (.xreg rd) (.vreg 1) bitmask)).run
        js_afterSourceSignExtend =
        .ok RETIRE_SUCCESS js_afterSrai := by
    simpa only [js_afterSrai] using h_virtual_srai_run

  have h_rd_reads_shifted_result :
      rX_bits rd s_afterSrai = .ok shiftedResult s_afterSrai := by
    exact wX_rX_roundtrip rd shiftedResult js.sail s_afterSrai hrd
      h_srai_writes_shifted_result

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes the SRAIW result.
  let sraiwResult := sign_extend (m := 64) (Sail.BitVec.extractLsb shiftedResult 31 0)
  have h_sraiw_result_eq_sail :
      sraiwResult =
        sign_extend (m := 64)
          (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
    simpa only [sraiwResult, shiftedResult, signedSource, bitmask] using
      virtual_sraiw_value_eq v shamt
  obtain ⟨s_afterSignExtend, h_sign_extend_run, h_sign_extend_write⟩ :=
    JoltISA.exists_state_after_virtual_sign_extend_word_run_xreg_xreg rd rd js_afterSrai
      shiftedResult (by simpa only [js_afterSrai] using h_rd_reads_shifted_result)
  have h_sign_extend_writes_result :
      wX_bits rd sraiwResult s_afterSrai = .ok () s_afterSignExtend := by
    simpa only [js_afterSrai, sraiwResult] using h_sign_extend_write

  let js' : SailJoltState :=
    { sail := s_afterSignExtend, vregs := js_afterSourceSignExtend.vregs }
  have h_sail_after_sign_extend :
      js'.sail = stateAfterWrite js_afterSrai.sail rd sraiwResult := by
    simpa only [js', js_afterSrai, sraiwResult] using
      wX_bits_eq_stateAfterWrite rd sraiwResult s_afterSrai s_afterSignExtend
        h_sign_extend_writes_result
  have h_sign_extend_succeeds :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_afterSrai =
        .ok RETIRE_SUCCESS js' := by
    simpa only [js'] using h_sign_extend_run

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' := by
    unfold JoltISA.sraiwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSourceSignExtend
      h_source_sign_extend_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSourceSignExtend js_afterSrai
      h_virtual_srai_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterSrai js' h_sign_extend_succeeds]
    rfl

  have h_sail_final :
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)) := by
    calc
      js'.sail = stateAfterWrite js_afterSrai.sail rd sraiwResult :=
        h_sail_after_sign_extend
      _ = stateAfterWrite (stateAfterWrite js.sail rd shiftedResult) rd sraiwResult := by
        rw [h_sail_after_srai]
      _ = stateAfterWrite js.sail rd sraiwResult := by
        exact stateAfterWrite_stateAfterWrite rd shiftedResult sraiwResult js.sail
      _ = stateAfterWrite js.sail rd
            (sign_extend (m := 64)
              (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)) := by
        rw [h_sraiw_result_eq_sail]

  exact ⟨js', v, hok, h_program_succeeds, h_sail_final⟩

/-- Main program-level equivalence for `SRAIW`. -/
theorem sraiwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.sraiwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
    (execute_SHIFTIWOP_SRAIW_factored shamt rs1 rd)
    (sraiwProgram_concrete shamt rs1 rd hrd js hwf)

end
