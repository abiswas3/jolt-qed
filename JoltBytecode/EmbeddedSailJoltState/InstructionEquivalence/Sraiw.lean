import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

-- From BytecodeExpansions/Instructions/Sraiw.lean
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

/-!
# SRAIW: Jolt 3-step decomposition = Sail SRAIW

Jolt decomposes SRAIW into three steps using a virtual register:
1. VirtualSignExtendWord rs1 → virtual register 1
2. VirtualSRAI virtual register 1 → rd (using bitmask)
3. VirtualSignExtendWord rd → rd

The bridge lemma (sraiw_three_step_value from BytecodeExpansions):
sign-extending a 32-bit value, logically right-shifting, then
truncating and sign-extending again equals directly doing an
arithmetic right shift on the 32-bit value.
-/

-- ============================================================================
-- Virtual register specs for mvcgen
-- ============================================================================

-- Writing to a virtual register always succeeds and only changes vregs.
@[spec]
theorem writeVReg_spec (vr : BitVec 7) (val : BitVec 64) (js0 : SailJoltState) :
    ⦃fun js => ⌜js = js0⌝⦄
    writeVReg vr val
    ⦃⇓ _ js' => ⌜js'.sail = js0.sail ∧
        js'.vregs = fun r => if r = vr then val else js0.vregs r⌝⦄ := by
  unfold writeVReg
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, bind, EStateM.bind,
             get, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply, PostCond.noThrow, SPred.pure]
  dsimp only [EStateM.run]
  exact ⟨rfl, rfl⟩

-- Reading from a virtual register always succeeds, returns the stored value,
-- and does not change the state.
@[spec]
theorem readVReg_spec (vr : BitVec 7) (js0 : SailJoltState) :
    ⦃fun js => ⌜js = js0⌝⦄
    readVReg vr
    ⦃⇓ v js' => ⌜v = js0.vregs vr ∧ js' = js0⌝⦄ := by
  unfold readVReg
  simp only [get, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply, PostCond.noThrow, SPred.pure]
  dsimp only [EStateM.run]
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- The three-step Jolt computation produces the same value as Sail's SRAIW.
-- This is the mathematical core: sign-extend, logical shift, truncate, sign-extend
-- equals arithmetic right shift then sign-extend.
-- LHS helper: the three-step Jolt value (sign-extend, shift, truncate, sign-extend)
-- equals sraiwJolt (the pure-function decomposition from BytecodeExpansions).
private lemma three_step_eq_sraiwJolt (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sraiwJolt v (shamt.setWidth 64) := by
  unfold sraiwJolt Jolt.virtualSignExtendWord sign_extend
  simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  congr 1

-- RHS helper: Sail's SRAIW value (extract 32 bits, arithmetic shift, sign-extend)
-- equals Riscv.sraiw (the reference RISC-V semantics from BytecodeExpansions).
private lemma sail_sraiw_eq_riscv (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) =
    Riscv.sraiw v (shamt.setWidth 64) := by
  unfold Riscv.sraiw sign_extend shift_bits_right_arith
  simp [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
        BitVec.extractLsb, BitVec.extractLsb']

-- Bridge: the three-step Jolt computation produces the same value as Sail's SRAIW.
-- Chains: LHS = sraiwJolt = Riscv.sraiw = RHS.
private lemma sraiw_three_step_value (v : BitVec 64) (shamt : BitVec 5) :
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
          ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0) =
    sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v 31 0) shamt) := by
  rw [three_step_eq_sraiwJolt, sail_sraiw_eq_riscv, sraiw_eq_sraiwJolt]

-- ============================================================================
-- Factoring
-- ============================================================================

-- The Sail execute_SHIFTIWOP for SRAIW reads rs1, extracts lower 32 bits,
-- arithmetically right-shifts by shamt, sign-extends to 64, writes to rd.
theorem execute_SHIFTIWOP_SRAIW_eq_factored (shamt : BitVec 5) (rs1 rd : regidx) :
    execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW = (do
      let v ← rX_bits rs1
      let rs1_32 := Sail.BitVec.extractLsb v 31 0
      wX_bits rd (sign_extend (m := 64) (shift_bits_right_arith rs1_32 shamt))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIWOP]

-- ============================================================================
-- Jolt SRAIW definition and mvcgen composition
-- ============================================================================

-- Jolt's SRAIW decomposition: three steps using a virtual register.
-- Step 1: Read rs1, sign-extend lower 32 bits, write to virtual register 1.
-- Step 2: Read virtual register 1, logical right shift by ctz(bitmask), write to rd.
-- Step 3: Read rd, sign-extend lower 32 bits, write to rd (VSEW).
def jolt_sraiw (shamt : BitVec 5) (rs1 rd : regidx) :
    JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  writeVReg 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))
  let v_rs1 ← readVReg 1
  liftSail (wX_bits rd (v_rs1 >>> ctz (sraiw_bitmask (shamt.setWidth 64))))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- mvcgen composes the primitive specs (liftSail_rX, writeVReg, readVReg,
-- liftSail_wX, vsew) to characterize the full 3-step computation.
theorem jolt_sraiw_concrete (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_sraiw shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb
            (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0) >>>
              ctz (sraiw_bitmask (shamt.setWidth 64))) 31 0)) := by
  unfold jolt_sraiw
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  -- VC1: rd is readable after step 2 wrote to it.
  -- simp_all propagates state equalities from steps 1-4 to normalize s✝.sail,
  -- then rX_after_stateAfterWrite closes the goal.
  · simp_all only [and_imp]
    exact ⟨_, rX_after_stateAfterWrite rd _ _ hrd⟩
  -- VC2: connect the 5-step chain to the existential conclusion.
  -- simp_all normalizes all intermediate states, then we provide witnesses.
  · -- Propagate all state equalities, collapse double writes, resolve reads-after-writes.
    -- simp_all chains hypotheses (s✝¹.sail = stateAfterWrite ...) as rewrites.
    simp_all [stateAfterWrite_stateAfterWrite, rX_after_stateAfterWrite _ _ _ hrd,
              EStateM.Result.ok.injEq, true_and]

-- ============================================================================
-- Main theorem: Jolt SRAIW = Sail SRAIW
-- ============================================================================

-- Running Jolt's three-step SRAIW decomposition and projecting onto Sail state
-- produces exactly the same result as running Sail's native SRAIW instruction.
-- The bridge is sraiw_three_step_value: the bitmask-based decomposition with
-- virtual registers equals the direct arithmetic right shift.
theorem jolt_sraiw_eq_sail (shamt : BitVec 5) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_sraiw shamt rs1 rd).run js) =
    (execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_sraiw_concrete shamt rs1 rd hrd js hwf
  -- Sail side: unfold and rewrite with the same v
  rw [execute_SHIFTIWOP_SRAIW_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  -- Jolt side: rewrite with concrete result
  show projectResult ((jolt_sraiw shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  -- Bridge: three-step Jolt value = arithmetic right shift
  rw [sraiw_three_step_value]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
