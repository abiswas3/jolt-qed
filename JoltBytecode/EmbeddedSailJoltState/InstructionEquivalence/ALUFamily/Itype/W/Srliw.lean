import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family
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

theorem execute_SHIFTIWOP_SRLIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP, bind_pure_comp, pure_bind]

def jolt_srliw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg 0 (v <<< 32)
  let v_rs1 ← readVReg 0
  liftSail (wX_bits rd (v_rs1 >>> ctz (srliw_imm (shamt.setWidth 64))))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_srliw_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_srliw shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  unfold jolt_srliw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get]
  obtain ⟨v, hok⟩ := hwf rs1
  simp only [hok]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true]
  obtain ⟨s3, hw1⟩ := wX_shape rd ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb ((v <<< 32) >>> ctz (srliw_imm (shamt.setWidth 64))) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v, rfl, rfl, ?_⟩
  rw [← srliw_shift_eq v shamt]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

theorem jolt_srliw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srliw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb v 31 0) shamt))
    (execute_SHIFTIWOP_SRLIW_factored shamt rs1 rd)
    (jolt_srliw_concrete shamt rs1 rd hrd js hwf)

end
