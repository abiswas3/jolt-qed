import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Family
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAIW: Jolt 3-step decomposition = Sail SRAIW

Jolt decomposes SRAIW using a virtual register:
1. `VirtualSignExtendWord rs1 → v1`
2. `VirtualSRAI rd, v1` via bitmask
3. `VirtualSignExtendWord rd`
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

def sraiwJolt (rs1_val shamt : BitVec 64) : BitVec 64 :=
  let v_rs1     := Jolt.virtualSignExtendWord rs1_val
  let v_bitmask := sraiw_bitmask shamt
  let v_result  := v_rs1 >>> ctz v_bitmask
  Jolt.virtualSignExtendWord v_result

theorem sraiw_eq_sraiwJolt (rs1_val shamt : BitVec 64) :
    Riscv.sraiw rs1_val shamt = sraiwJolt rs1_val shamt := by
  unfold Riscv.sraiw sraiwJolt Jolt.virtualSignExtendWord
  simp only [ctz_sraiw_bitmask]
  have hs : (shamt.setWidth 5).toNat < 32 := by
    have := (shamt.setWidth 5).isLt; norm_num at this; exact this
  congr 1
  rw [sshiftRight_eq_signExtend_ushr_trunc (rs1_val.setWidth 32) _ hs]

private lemma three_step_eq_sraiwJolt (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sraiwJolt v (shamt.setWidth 64) := by
  unfold sraiwJolt Jolt.virtualSignExtendWord sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 1

private lemma sail_sraiw_eq_riscv (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) =
    Riscv.sraiw v (shamt.setWidth 64) := by
  unfold Riscv.sraiw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

private lemma sraiw_three_step_value (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [three_step_eq_sraiwJolt, sail_sraiw_eq_riscv, sraiw_eq_sraiwJolt]

theorem execute_SHIFTIWOP_SRAIW_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW = (do
      let v ← rX_bits rs1
      wX_bits rd (sign_extend (m := 64)
        (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

def jolt_sraiw (shamt : BitVec 5) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  let v_rs1 ← readVReg 1
  liftSail (wX_bits rd (v_rs1 >>> ctz (sraiw_bitmask (shamt.setWidth 64))))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_sraiw_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_sraiw shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt)) := by
  unfold jolt_sraiw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get, MonadStateOf.get, EStateM.get]
  obtain ⟨v, hok⟩ := hwf rs1
  simp only [hok]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true, ite_false]
  obtain ⟨s3, hw1⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>> ctz (sraiw_bitmask (shamt.setWidth 64))) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>> ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v, rfl, rfl, ?_⟩
  rw [← sraiw_three_step_value v shamt]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

theorem jolt_sraiw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sraiw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run js.sail :=
  itype_eq_sail_uniform
    (f := fun v => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt))
    (execute_SHIFTIWOP_SRAIW_factored shamt rs1 rd)
    (jolt_sraiw_concrete shamt rs1 rd hrd js hwf)

end
