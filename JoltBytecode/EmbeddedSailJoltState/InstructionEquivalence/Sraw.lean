import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

-- From BytecodeExpansions/Instructions/Sraw.lean
def sraw_bitmask (shamt_val : BitVec 64) : Nat :=
  let shift := (shamt_val.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

lemma ctz_sraw_bitmask (shamt_val : BitVec 64) :
    ctz (sraw_bitmask shamt_val) = (shamt_val.setWidth 6).toNat := by
  unfold sraw_bitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (shamt_val.setWidth 6).toNat
  have h_lt : shift < 64 := by have := (shamt_val.setWidth 6).isLt; norm_num at this; exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]; omega

private lemma ctz_sraw_chain (rs2_val : BitVec 64) :
    ctz (sraw_bitmask (Riscv.andi rs2_val 0x1f#64)) = (rs2_val.setWidth 5).toNat := by
  rw [ctz_sraw_bitmask]
  unfold Riscv.andi
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : (31 : Nat) % 2 ^ 64 = 31 := by norm_num
  rw [h1, show (31 : Nat) = 2 ^ 5 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt rs2_val.toNat (show 0 < 2 ^ 5 from by positivity); omega)

def srawJolt (rs1_val rs2_val : BitVec 64) : BitVec 64 :=
  let v_rs1     := Jolt.virtualSignExtendWord rs1_val
  let v_shamt   := Riscv.andi rs2_val 0x1f#64
  let v_bitmask := sraw_bitmask v_shamt
  let v_result  := v_rs1 >>> ctz v_bitmask
  Jolt.virtualSignExtendWord v_result

theorem sraw_eq_srawJolt (rs1_val rs2_val : BitVec 64) :
    Riscv.sraw rs1_val rs2_val = srawJolt rs1_val rs2_val := by
  unfold Riscv.sraw srawJolt Jolt.virtualSignExtendWord
  simp only [ctz_sraw_chain]
  have hs : (rs2_val.setWidth 5).toNat < 32 := by
    have := (rs2_val.setWidth 5).isLt; norm_num at this; exact this
  congr 1
  rw [sshiftRight_eq_signExtend_ushr_trunc (rs1_val.setWidth 32) _ hs]

/-! ## SRAW: Jolt 5-step decomposition = Sail SRAW

Jolt decomposes SRAW into 5 steps (from BytecodeExpansions/Sraw.lean):
1. VirtualSignExtendWord rs1 → v_rs1    (sign-extend rs1[31:0] to 64)
2. ANDI rs2, 0x1f → v_shamt             (mask shift amount to 5 bits)
3. VirtualShiftRightBitmask → v_bitmask  (compute bitmask from shift)
4. VirtualSRA v_rs1, v_bitmask → rd      (arith right shift via ctz(bitmask))
5. VirtualSignExtendWord rd → rd          (sign-extend result)

Sail's SRAW extracts lower 32 bits of rs1, arithmetically right-shifts
by rs2[4:0], sign-extends to 64, writes to rd.
-/

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- The 5-step Jolt computation produces the same value as Sail's SRAW.
-- Sign-extend, mask shift, shift via bitmask, sign-extend =
-- direct 32-bit arithmetic right shift then sign-extend.
-- Uses sraw_eq_srawJolt from BytecodeExpansions.
-- LHS helper: the Jolt 5-step value (sign-extend, mask, shift via bitmask,
-- sign-extend) equals srawJolt (the pure-function decomposition).
private lemma five_step_eq_srawJolt (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>>
          ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0) =
    srawJolt v1 v2 := by
  unfold srawJolt Jolt.virtualSignExtendWord sign_extend Riscv.andi
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 2

-- RHS helper: Sail's SRAW value (extract 32, arith shift, sign-extend)
-- equals Riscv.sraw (the reference semantics).
private lemma sail_sraw_eq_riscv (v1 v2 : BitVec 64) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) =
    Riscv.sraw v1 v2 := by
  unfold Riscv.sraw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']
  congr 2

-- The 5-step Jolt SRAW computation produces the same value as Sail's SRAW.
-- Chains: LHS = srawJolt = Riscv.sraw = RHS.
private lemma sraw_five_step_value (v1 v2 : BitVec 64) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>>
          ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)) := by
  rw [five_step_eq_srawJolt, sail_sraw_eq_riscv, sraw_eq_srawJolt]

-- ============================================================================
-- Factoring
-- ============================================================================

-- Sail's SRAW reads rs1, extracts lower 32 bits, arithmetically right-shifts
-- by the lower 5 bits of rs2, sign-extends to 64, writes to rd.
theorem execute_RTYPEW_SRAW_eq_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SRAW = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith
        (Sail.BitVec.extractLsb v1 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0)))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind, bind_assoc]

-- ============================================================================
-- Jolt SRAW definition (faithful to BytecodeExpansions/Sraw.lean)
-- ============================================================================

-- Jolt's SRAW decomposition: 5 steps with virtual registers.
-- Step 1: Sign-extend rs1[31:0] to 64, store in v_rs1.
-- Step 2: Mask rs2 shift amount to 5 bits (ANDI 0x1f), store in v_shamt.
-- Step 3: Compute bitmask from v_shamt (VirtualShiftRightBitmask).
-- Step 4: Arithmetic right shift v_rs1 by ctz(bitmask), write to rd.
-- Step 5: Sign-extend rd[31:0] (VirtualSignExtendWord).
def jolt_sraw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  -- Step 1: VirtualSignExtendWord rs1 → virtual register 0
  let v1 ← liftSail (rX_bits rs1)
  writeVReg 0 (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
  -- Step 2: ANDI rs2, 0x1f → virtual register 1
  let v2 ← liftSail (rX_bits rs2)
  writeVReg 1 (v2 &&& 0x1f#64)
  -- Step 3-4: VirtualSRA using bitmask of v_shamt, write to rd
  let v_rs1 ← readVReg 0
  let v_shamt ← readVReg 1
  liftSail (wX_bits rd (v_rs1 >>> ctz (sraw_bitmask v_shamt)))
  -- Step 5: VirtualSignExtendWord rd
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Concrete characterization
-- ============================================================================

-- After running Jolt's SRAW, rd holds the Sail SRAW value.
theorem jolt_sraw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_sraw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
          (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))) := by
  unfold jolt_sraw jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
             writeVReg, readVReg, modify, modifyGet, MonadStateOf.modifyGet,
             EStateM.modifyGet, get, MonadStateOf.get, EStateM.get]
  obtain ⟨v1, hok1⟩ := hwf rs1
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok1, hok2]
  dsimp only [getThe, MonadStateOf.get, EStateM.get]
  simp (config := { decide := true }) only [ite_true, ite_false]
  obtain ⟨s3, hw1⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>> ctz (sraw_bitmask (v2 &&& 0x1f#64))) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  simp only [hrx]
  obtain ⟨s4, hw2⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0) >>> ctz (sraw_bitmask (v2 &&& 0x1f#64))) 31 0)) s3
  simp only [hw2]
  have hc := wX_wX_collapse rd _ _ js.sail s3 s4 hw1 hw2
  refine ⟨_, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [← sraw_five_step_value v1 v2]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s4 hc

-- ============================================================================
-- Main theorem: Jolt SRAW = Sail SRAW
-- ============================================================================

-- Running Jolt's 5-step SRAW decomposition and projecting onto Sail state
-- produces exactly the same result as running Sail's native SRAW instruction.
-- The bridge is sraw_five_step_value: the bitmask-based decomposition with
-- sign-extension and masking equals the direct arithmetic right shift.
theorem jolt_sraw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sraw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_sraw_concrete rs2 rs1 rd hrd js hwf
  rw [execute_RTYPEW_SRAW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_sraw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
