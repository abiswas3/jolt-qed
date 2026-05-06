import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Expansions.ALU
import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.StraightLine
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLIW: Jolt SLLI 32 + VirtualSRLI + VSEW = Sail SRLIW

Jolt decomposes SRLIW via the bitmask encoding:
1. `SLLI v0, rs1, 32`
2. `VirtualSRLI rd, v0, bitmask` where bitmask = `srliw_imm shamt`
3. `VirtualSignExtendWord rd`

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
  ext i; simp [BitVec.getLsbD_setWidth]

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

private theorem virtual_srliw_value_eq (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (jolt_virtual_srli_value (shift_bits_left v (32 : BitVec 6))
          (JoltISA.srliwBitmask shamt)) 31 0) =
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [srliwProgram_bitmask_eq]
  simpa [jolt_virtual_srli_value, shift_bits_left] using srliw_shift_eq v shamt

theorem execute_SHIFTIWOP_SRLIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind]

/-- Program-level concrete theorem for `SRLIW`.

The program shifts `rs1` left into scratch `v0`, applies `VirtualSRLI` with the
encoded immediate bitmask, and then sign-extends `rd`. -/
theorem srliwProgram_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (JoltISA.execProgram (JoltISA.srliwProgram shamt rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  obtain ⟨v, hok⟩ := hwf rs1
  let shifted := shift_bits_left v (32 : BitVec 6)
  let raw := jolt_virtual_srli_value shifted (JoltISA.srliwBitmask shamt)
  let js_shift : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : JoltISA.VReg) then shifted else js.vregs r }
  have hslli :
      (JoltISA.execInstr (.SLLI (.vreg 0) (.xreg rs1) (32 : BitVec 6))).run js =
        .ok RETIRE_SUCCESS js_shift := by
    simpa [js_shift, shifted] using
      (JoltISA.execInstr_slli_xreg_vreg_run (0 : JoltISA.VReg) rs1
        (32 : BitVec 6) js v hok)
  obtain ⟨s_raw, hw_raw⟩ := wX_shape rd raw js.sail
  let js_raw : SailJoltState := { sail := s_raw, vregs := js_shift.vregs }
  have hsrli :
      (JoltISA.execInstr (.VirtualSRLI (.xreg rd) (.vreg 0) (JoltISA.srliwBitmask shamt))).run js_shift =
        .ok RETIRE_SUCCESS js_raw := by
    have hwrite :
        wX_bits rd (jolt_virtual_srli_value (js_shift.vregs (0 : JoltISA.VReg))
          (JoltISA.srliwBitmask shamt)) js_shift.sail = .ok () s_raw := by
      simpa [js_shift, raw, shifted] using hw_raw
    simpa [js_raw] using
      (JoltISA.execInstr_virtualSRLI_vreg_xreg_run rd (0 : JoltISA.VReg)
        (JoltISA.srliwBitmask shamt) js_shift s_raw hwrite)
  have hread_rd : rX_bits rd js_raw.sail = .ok raw js_raw.sail := by
    simpa [js_raw] using (wX_rX_roundtrip rd raw js.sail s_raw hrd hw_raw)
  let final := sign_extend (m := 64) (Sail.BitVec.extractLsb raw 31 0)
  obtain ⟨s_final, hw_final⟩ := wX_shape rd final js_raw.sail
  let js' : SailJoltState := { sail := s_final, vregs := js_shift.vregs }
  have hsextw :
      (JoltISA.execInstr (.SExtW (.xreg rd) (.xreg rd))).run js_raw =
        .ok RETIRE_SUCCESS js' := by
    simpa [js', final] using
      (JoltISA.execInstr_sextw_xreg_xreg_run rd rd js_raw raw s_final
        hread_rd hw_final)
  refine ⟨js', v, hok, ?_, ?_⟩
  · unfold JoltISA.srliwProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_shift hslli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_raw hsrli]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_raw js' hsextw]
    rfl
  · dsimp [js']
    have hc := wX_wX_collapse rd raw final js.sail s_raw s_final hw_raw hw_final
    rw [wX_bits_eq_stateAfterWrite rd _ js.sail s_final hc]
    dsimp [final, raw, shifted]
    congr 1
    simpa using virtual_srliw_value_eq v shamt

/-- Main program-level equivalence for `SRLIW`. -/
theorem srliwProgram_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((JoltISA.execProgram (JoltISA.srliwProgram shamt rs1 rd)).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))
    (execute_SHIFTIWOP_SRLIW_factored shamt rs1 rd)
    (srliwProgram_concrete shamt rs1 rd hrd js hwf)

end
