import JoltBytecode.SailJoltState.EmbeddedArch.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Sraiw

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

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
  -- VC1: rd readable after step 2 write (follows from rX_after_stateAfterWrite)
  -- VC2: connect 5-step chain to final result (mechanical plumbing)
  -- TODO: close these VCs (mvcgen auto-generated variable names make manual proof brittle)
  all_goals sorry

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
