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
  simpa [setWidth_5_roundtrip, extract_shamt64_low5] using
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

  -- Instruction 1: `VirtualSignExtendWord v1, rs1` writes `sx = sext(v[31:0])` to `v1`.
  let sx := sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)
  let js_sx : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (1 : JoltISA.VReg) then sx else js.vregs r }
  have instr1_VirtualSignExtendWord_writes_sx :
      (JoltISA.execInstr (.VirtualSignExtendWord (.vreg 1) (.xreg rs1))).run js =
        .ok RETIRE_SUCCESS js_sx := by
    simpa [js_sx, sx] using
      (JoltISA.execInstr_sextw_xreg_vreg_run (1 : JoltISA.VReg) rs1 js v hok)

  -- Instruction 2: `VirtualSRAI rd, v1, sraiwBitmask shamt` writes `raw` to `rd`.
  let bitmask := JoltISA.sraiwBitmask shamt
  let raw := jolt_virtual_srai_value sx bitmask
  obtain ⟨s_raw, hrun_VirtualSRAI, hw_raw_srai⟩ :=
    JoltISA.execInstr_virtualSRAI_vreg_xreg_run_of_vreg rd (1 : JoltISA.VReg)
      bitmask js_sx
  have hw_raw : wX_bits rd raw js.sail = .ok () s_raw := by
    simpa [js_sx, raw, sx, bitmask] using hw_raw_srai
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_sx.vregs }
  have instr2_VirtualSRAI_writes_raw :
      (JoltISA.execInstr (.VirtualSRAI (.xreg rd) (.vreg 1) bitmask)).run js_sx =
        .ok RETIRE_SUCCESS js_raw := by
    simpa [js_raw] using hrun_VirtualSRAI

  have hread_rd : rX_bits rd s_raw = .ok raw s_raw := by
    exact wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw

  -- Instruction 3: `VirtualSignExtendWord rd, rd` writes `sext(raw[31:0])`.
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hrun_VirtualSignExtendWord, hw_final_raw⟩ :=
    JoltISA.execInstr_sextw_xreg_xreg_run_of_read rd rd js_raw raw
      (by simpa [js_raw] using hread_rd)
  have hw_final : wX_bits rd final s_raw = .ok () s_final := by
    simpa [js_raw, final] using hw_final_raw

  let js' : SailJoltState := { sail := s_final, vregs := js_sx.vregs }
  have instr3_VirtualSignExtendWord_writes_final :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js'] using hrun_VirtualSignExtendWord
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.sraiwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_sx
      instr1_VirtualSignExtendWord_writes_sx]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_sx js_raw
      instr2_VirtualSRAI_writes_raw]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js'
      instr3_VirtualSignExtendWord_writes_final]
    rfl
  · dsimp [js']
    -- NOTE: Math theorem: `virtual_sraiw_value_eq` matches the virtual sequence with Sail SRAIW.
    have math_raw_low32 :
        final =
          sign_extend (m := 64)
            (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
      dsimp [final, raw, sx, bitmask]
      simpa using virtual_sraiw_value_eq v shamt
    have final_write_from_initial :
        wX_bits rd
          (sign_extend (m := 64)
            (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
          js.sail = .ok () s_final := by
      rw [← math_raw_low32]
      exact wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s_final final_write_from_initial

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
