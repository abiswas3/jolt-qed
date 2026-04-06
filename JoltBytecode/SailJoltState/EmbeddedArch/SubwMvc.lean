import JoltBytecode.SailJoltState.EmbeddedArch.AddwMvc

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## SUBW via mvcgen (reuses vsew_spec from AddwMvc) -/

-- Mathematical core: truncation distributes over subtraction.
theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

def jolt_subw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- New spec: SUB instead of ADD. Same structure, just v1 - v2.
@[spec]
theorem liftSail_SUB_spec (rs2 rs1 rd : regidx) (js0 : SailJoltState)
    (hwf : WellFormed js0) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
    ⦃⇓ r js' => ⌜r = RETIRE_SUCCESS ∧
      ∃ (v1 v2 : BitVec 64),
        rX_bits rs1 js0.sail = .ok v1 js0.sail ∧
        rX_bits rs2 js0.sail = .ok v2 js0.sail ∧
        js'.sail = stateAfterWrite js0.sail rd (v1 - v2)⌝⦄ := by
  unfold liftSail execute_RTYPE
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply]
  dsimp only [EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  simp only [hok1]
  obtain ⟨v2, hok2⟩ := hwf rs2
  simp only [hok2]
  obtain ⟨s3, hw⟩ := wX_shape rd (v1 - v2) js.sail
  simp only [hw, PostCond.noThrow, SPred.pure]
  exact ⟨trivial, v1, v2, rfl, rfl, wX_bits_eq_stateAfterWrite rd (v1 - v2) js.sail s3 hw⟩

-- mvcgen composes liftSail_SUB_spec + vsew_spec (reused from AddwMvc).
theorem jolt_subw_concrete (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 : BitVec 64) (v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_subw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (v1 - v2) 31 0)) := by
  unfold jolt_subw
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  · rename_i r1 s1 h_sub
    obtain ⟨rfl, v1, v2, h_rx1, h_rx2, h_proj1⟩ := h_sub
    rw [h_proj1]
    exact ⟨v1 - v2, rX_after_stateAfterWrite rd (v1 - v2) js.sail hrd⟩
  · rename_i r1 s1 h_sub r2 s2 h_vsew
    obtain ⟨rfl, v1, v2, h_rx1, h_rx2, h_proj1⟩ := h_sub
    obtain ⟨v, h_rxrd, h_proj2⟩ := h_vsew
    refine ⟨s2, v1, v2, h_rx1, h_rx2, rfl, ?_⟩
    rw [h_proj2, h_proj1, stateAfterWrite_stateAfterWrite]
    rw [h_proj1] at h_rxrd
    rw [rX_after_stateAfterWrite rd (v1 - v2) js.sail hrd] at h_rxrd
    have h_v : v = v1 - v2 := (EStateM.Result.ok.inj h_rxrd).1.symm
    rw [h_v]

-- Main theorem: Jolt SUBW = Sail SUBW
theorem jolt_subw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_subw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_subw_concrete rs2 rs1 rd hrd js hwf
  unfold execute_RTYPEW
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_subw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0 -
     Sail.BitVec.extractLsb v2 31 0)) js.sail
  simp only [hw]
  have hs' := wX_bits_eq_stateAfterWrite rd _ js.sail s' hw
  rw [hs']
  unfold stateAfterWrite
  simp only [extractLsb_sub]

end
