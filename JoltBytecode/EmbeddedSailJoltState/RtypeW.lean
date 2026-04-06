import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import Std.Tactic.Do

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# Generic R-type W instruction equivalence via mvcgen

All R-type W instructions (ADDW, SUBW, ...) follow the same pattern:
- Jolt: execute_RTYPE op (64-bit) then jolt_virtual_sign_extend_word
- Sail: execute_RTYPEW opw (truncate to 32, compute, sign-extend)
- The only unique parts per instruction are:
  1. A factoring lemma for execute_RTYPE with the specific op
  2. The mathematical core (extractLsb distributes over the operation)

This file provides the shared infrastructure. Per-instruction files
supply the factoring lemma, the math lemma, and instantiate.
-/

-- ============================================================================
-- WellFormed: all register reads succeed
-- ============================================================================

-- A state is well-formed if all register reads succeed.
-- This holds for any real RISC-V state (registers are always initialized).
def WellFormed (js : SailJoltState) : Prop :=
  ∀ r : regidx, ∃ v, rX_bits r js.sail = .ok v js.sail

-- ============================================================================
-- Primitive specs: liftSail(rX_bits) and liftSail(wX_bits)
-- ============================================================================

-- Reading register r via liftSail succeeds (given WellFormed), returns the
-- register value, and does not change the state.
@[spec]
theorem liftSail_rX_spec (r : regidx) (js0 : SailJoltState) (hwf : WellFormed js0) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (rX_bits r)
    ⦃⇓ v js' => ⌜rX_bits r js0.sail = .ok v js0.sail ∧ js' = js0⌝⦄ := by
  unfold liftSail
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply, PostCond.noThrow, SPred.pure]
  dsimp only [EStateM.run]
  obtain ⟨v, hok⟩ := hwf r
  rw [hok]
  cases js
  exact ⟨rfl, rfl⟩

-- Writing value v to register r via liftSail always succeeds and updates
-- the sail state to stateAfterWrite.
@[spec]
theorem liftSail_wX_spec (r : regidx) (v : BitVec 64) (js0 : SailJoltState) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (wX_bits r v)
    ⦃⇓ _ js' => ⌜js'.sail = stateAfterWrite js0.sail r v ∧ js'.vregs = js0.vregs⌝⦄ := by
  unfold liftSail
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply, PostCond.noThrow, SPred.pure]
  dsimp only [EStateM.run]
  obtain ⟨s', hw⟩ := wX_shape r v js.sail
  rw [hw]
  exact ⟨wX_bits_eq_stateAfterWrite r v js.sail s' hw, by cases js; rfl⟩

-- ============================================================================
-- Generic R-type spec (parameterized by a factoring hypothesis)
-- ============================================================================

-- Spec for liftSail(execute_RTYPE) given that the op factors as:
--   do let v1 ← rX_bits rs1; let v2 ← rX_bits rs2; wX_bits rd (f v1 v2); pure RETIRE_SUCCESS
-- Each concrete op provides the factoring proof (typically by `unfold execute_RTYPE; rfl`).
@[spec]
theorem liftSail_RTYPE_spec (rs2 rs1 rd : regidx) (op : rop)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : execute_RTYPE rs2 rs1 rd op = do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (f v1 v2); pure RETIRE_SUCCESS)
    (js0 : SailJoltState) (hwf : WellFormed js0) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (execute_RTYPE rs2 rs1 rd op)
    ⦃⇓ r js' => ⌜r = RETIRE_SUCCESS ∧
      ∃ (v1 v2 : BitVec 64),
        rX_bits rs1 js0.sail = .ok v1 js0.sail ∧
        rX_bits rs2 js0.sail = .ok v2 js0.sail ∧
        js'.sail = stateAfterWrite js0.sail rd (f v1 v2)⌝⦄ := by
  rw [hf]
  unfold liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply]
  dsimp only [EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  simp only [hok1]
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok2]
  obtain ⟨s3, hw⟩ := wX_shape rd (f v1 v2) js.sail
  simp only [hw, PostCond.noThrow, SPred.pure]
  exact ⟨trivial, v1, v2, rfl, rfl, wX_bits_eq_stateAfterWrite rd (f v1 v2) js.sail s3 hw⟩

-- ============================================================================
-- vsew_spec: total correctness given rd is readable
-- ============================================================================

-- After a write to rd, the virtual-sign-extend-word reads rd back,
-- sign-extends the lower 32 bits, and writes the result.
-- Precondition hrd_ok is discharged by mvcgen from the RTYPE spec.
@[spec]
theorem vsew_spec (rd : regidx) (js0 : SailJoltState) (hrd : rd ≠ regidx.Regidx 0)
    (hrd_ok : ∃ v, rX_bits rd js0.sail = .ok v js0.sail) :
    ⦃fun js => ⌜js = js0⌝⦄
    jolt_virtual_sign_extend_word rd
    ⦃⇓ _ js' => ⌜∃ v,
        rX_bits rd js0.sail = .ok v js0.sail ∧
        js'.sail = stateAfterWrite js0.sail rd
          (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))⌝⦄ := by
  unfold jolt_virtual_sign_extend_word liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply, PostCond.noThrow, SPred.pure]
  dsimp only [EStateM.run, EStateM.bind]
  obtain ⟨v, hok⟩ := hrd_ok
  simp only [hok]
  obtain ⟨s', hw⟩ := wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)) js.sail
  simp only [hw]
  exact ⟨v, rfl, wX_bits_eq_stateAfterWrite rd _ js.sail s' hw⟩

-- ============================================================================
-- Generic Jolt R-type W definition and mvcgen composition
-- ============================================================================

-- Jolt decomposes any R-type W instruction as: execute_RTYPE op, then VSEW, then return.
def jolt_rtype_w (op : rop) (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd op)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- mvcgen composes liftSail_RTYPE_spec + vsew_spec to characterize the result.
-- The factoring hypothesis hf is per-instruction (typically proved by rfl).
theorem jolt_rtype_w_concrete (op : rop)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ rs2 rs1 rd, execute_RTYPE rs2 rs1 rd op = do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (f v1 v2); pure RETIRE_SUCCESS)
    (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 : BitVec 64) (v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_rtype_w op rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (f v1 v2) 31 0)) := by
  unfold jolt_rtype_w
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  · -- VC: factoring hypothesis for the RTYPE spec
    exact hf rs2 rs1 rd
  · -- VC: hrd_ok — rd is readable after the write
    rename_i r1 s1 h_op
    obtain ⟨rfl, v1, v2, h_rx1, h_rx2, h_proj1⟩ := h_op
    rw [h_proj1]
    exact ⟨f v1 v2, rX_after_stateAfterWrite rd (f v1 v2) js.sail hrd⟩
  · -- Main VC: connect the results
    rename_i r1 s1 h_op r2 s2 h_vsew
    obtain ⟨rfl, v1, v2, h_rx1, h_rx2, h_proj1⟩ := h_op
    obtain ⟨v, h_rxrd, h_proj2⟩ := h_vsew
    refine ⟨s2, v1, v2, h_rx1, h_rx2, rfl, ?_⟩
    rw [h_proj2, h_proj1, stateAfterWrite_stateAfterWrite]
    rw [h_proj1] at h_rxrd
    rw [rX_after_stateAfterWrite rd (f v1 v2) js.sail hrd] at h_rxrd
    have h_v : v = f v1 v2 := (EStateM.Result.ok.inj h_rxrd).1.symm
    rw [h_v]

-- ============================================================================
-- Generic main theorem (parameterized by the math lemma)
-- ============================================================================

-- The math lemma connects the 64-bit operation with the 32-bit W operation.
-- Each instruction provides this lemma (e.g., extractLsb_add for ADDW).
theorem jolt_rtype_w_eq_sail (op : rop) (opw : ropw)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ rs2 rs1 rd, execute_RTYPE rs2 rs1 rd op = do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (f v1 v2); pure RETIRE_SUCCESS)
    (h_math : ∀ a b : BitVec 64,
      Sail.BitVec.extractLsb (f a b) 31 0 =
      (match opw with
        | ropw.ADDW => Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0
        | ropw.SUBW => Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0
        | ropw.SLLW => shift_bits_left (Sail.BitVec.extractLsb a 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0)
        | ropw.SRLW => shift_bits_right (Sail.BitVec.extractLsb a 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0)
        | ropw.SRAW => shift_bits_right_arith (Sail.BitVec.extractLsb a 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb b 31 0) 4 0)))
    (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_rtype_w op rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd opw).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_rtype_w_concrete op f hf rs2 rs1 rd hrd js hwf
  unfold execute_RTYPEW
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_rtype_w op rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  -- Goal: stateAfterWrite(signext(extractLsb(f v1 v2))) = stateAfterWrite(signext(opw_result))
  -- Apply the math lemma to connect them.
  rw [h_math]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
