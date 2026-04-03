import JoltBytecode.SailJoltState.RegisterLemmas
import Std.Tactic.Do

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

noncomputable def stateAfterWrite (s : SailState) (rd : regidx) (val : BitVec 64) : SailState :=
  { s with regs := wX_update_regs rd val s.regs }

def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Specs: what each operation does, given KNOWN read values.
-- These are parameterized by v1, v2 so both sides share the same values.
-- ============================================================================

-- After liftSail(execute_RTYPE ADD), given that rs1 reads v1 and rs2 reads v2,
-- the result is RETIRE_SUCCESS and the projected state has rd = v1+v2.
@[spec]
theorem liftSail_ADD_spec (rs2 rs1 rd : regidx) (js0 : SailJoltState) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
    ⦃⇓ r js' => ⌜r = RETIRE_SUCCESS ∧
      ∃ (v1 v2 : BitVec 64),
        rX_bits rs1 (project js0) = .ok v1 (project js0) ∧
        rX_bits rs2 (project js0) = .ok v2 (project js0) ∧
        project js' = stateAfterWrite (project js0) rd (v1 + v2)⌝⦄ := by
  sorry

@[spec]
theorem vsew_spec (rd : regidx) (js0 : SailJoltState) (hrd : rd ≠ regidx.Regidx 0) :
    ⦃fun js => ⌜js = js0⌝⦄
    jolt_virtual_sign_extend_word rd
    ⦃⇓ _ js' => ⌜∃ v,
        rX_bits rd (project js0) = .ok v (project js0) ∧
        project js' = stateAfterWrite (project js0) rd
          (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))⌝⦄ := by
  sorry

-- ============================================================================
-- Jolt side via mvcgen: given that reads succeed, what's the final state?
-- ============================================================================

theorem jolt_addw_concrete (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) :
    ∃ (js' : SailJoltState) (v1 : BitVec 64) (v2 : BitVec 64),
      rX_bits rs1 (project js) = .ok v1 (project js) ∧
      rX_bits rs2 (project js) = .ok v2 (project js) ∧
      (jolt_addw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      project js' = stateAfterWrite (project js) rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 + v2) 31 0)) := by
  unfold jolt_addw
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  rename_i r1 s1 h_add r2 s2 h_vsew
  obtain ⟨rfl, v1, v2, h_rx1, h_rx2, h_proj1⟩ := h_add
  obtain ⟨v, h_rxrd, h_proj2⟩ := h_vsew
  refine ⟨s2, v1, v2, h_rx1, h_rx2, rfl, ?_⟩
  rw [h_proj2, h_proj1]
  unfold stateAfterWrite
  simp only [wX_update_regs_idem]
  rw [h_proj1] at h_rxrd
  unfold stateAfterWrite at h_rxrd
  have h := rX_after_wX rd (v1 + v2) (project js) hrd
  rw [h] at h_rxrd
  have h_v : v = v1 + v2 := (EStateM.Result.ok.inj h_rxrd).1.symm
  rw [h_v]

-- ============================================================================
-- Main theorem: hybrid approach.
-- Use sail_cases for shared reads (connects v1,v2 across both sides).
-- Use jolt_addw_concrete for the Jolt plumbing.
-- The mathematical core is extractLsb_add.
-- ============================================================================

theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run (project js) := by
  -- Jolt side: concrete result with read equations.
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_proj⟩ := jolt_addw_concrete rs2 rs1 rd hrd js
  -- Sail side: unfold and use the SAME v1, v2 (by rewriting with the read equations).
  unfold execute_RTYPEW
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  -- Rewrite Jolt side with concrete result.
  show projectResult ((jolt_addw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult]
  rw [hj_proj]
  -- Goal: .ok RETIRE_SUCCESS (stateAfterWrite (project js) rd (signext(extractLsb(v1+v2))))
  --     = match wX_bits rd (signext(extractLsb(v1)+extractLsb(v2))) (project js) with ...
  -- Use wX_shape to get the Sail write result.
  obtain ⟨s', hw⟩ := wX_shape rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) (project js)
  simp only [hw]
  -- Goal: stateAfterWrite ... (signext(extractLsb(v1+v2))) = s'
  -- Use wX_regs_spec + wX_eq_modify_regs to characterize s'.
  have ⟨_, hw_ok, hw_regs⟩ := wX_regs_spec rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) (project js)
  have ⟨_, he⟩ := eStateM_deterministic hw hw_ok; subst he
  have hmod := wX_eq_modify_regs rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) (project js) s' hw
  -- s' = { project js with regs := s'.regs } and s'.regs = wX_update_regs ...
  rw [hmod]
  unfold stateAfterWrite
  rw [hw_regs]
  -- Goal: wX_update_regs rd (signext(extractLsb(v1+v2))) = wX_update_regs rd (signext(extractLsb(v1)+extractLsb(v2)))
  simp only [extractLsb_add]

end
