import JoltBytecode.SailJoltState.EmbeddedArch.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# ADDIW: Jolt ADDI + VirtualSignExtendWord = Sail ADDIW

Jolt decomposes ADDIW as:
1. ADDI rd, rs1, imm   — 64-bit add with sign-extended immediate
2. VSEW rd              — sign-extend lower 32 bits of rd

The math is trivial: both Jolt and Sail compute
  sign_extend(extractLsb(rs1 + sign_extend(imm), 31, 0))
so no extractLsb distribution lemma is needed.
-/

-- ============================================================================
-- Spec for liftSail(execute_ITYPE ADDI)
-- ============================================================================

-- Factoring: execute_ITYPE ADDI reads rs1, adds sign-extended immediate, writes to rd.
theorem execute_ITYPE_ADDI_factored (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ITYPE imm rs1 rd iop.ADDI = (do
      let v1 ← rX_bits rs1
      wX_bits rd (v1 + sign_extend (m := 64) imm)
      pure RETIRE_SUCCESS) := by
  simp [execute_ITYPE, bind_pure_comp, pure_bind]

-- After running Jolt's ADDI, the result is RETIRE_SUCCESS and rd holds v1 + sign_extend(imm).
@[spec]
theorem liftSail_ADDI_spec (imm : BitVec 12) (rs1 rd : regidx) (js0 : SailJoltState)
    (hwf : WellFormed js0) :
    ⦃fun js => ⌜js = js0⌝⦄
    liftSail (execute_ITYPE imm rs1 rd iop.ADDI)
    ⦃⇓ r js' => ⌜r = RETIRE_SUCCESS ∧
      ∃ (v1 : BitVec 64),
        rX_bits rs1 js0.sail = .ok v1 js0.sail ∧
        js'.sail = stateAfterWrite js0.sail rd (v1 + sign_extend (m := 64) imm)⌝⦄ := by
  rw [execute_ITYPE_ADDI_factored]
  unfold liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  intro js hjs; subst hjs
  simp only [WP.wp, PredTrans.apply]
  dsimp only [EStateM.run]
  obtain ⟨v1, hok1⟩ := hwf rs1
  simp only [hok1]
  obtain ⟨s2, hw⟩ := wX_shape rd (v1 + sign_extend (m := 64) imm) js.sail
  simp only [hw, PostCond.noThrow, SPred.pure]
  exact ⟨trivial, v1, rfl, wX_bits_eq_stateAfterWrite rd _ js.sail s2 hw⟩

-- ============================================================================
-- Jolt ADDIW definition and mvcgen composition
-- ============================================================================

-- Jolt's ADDIW decomposition: 64-bit ADDI then sign-extend lower 32 bits.
def jolt_addiw (imm : BitVec 12) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_ITYPE imm rs1 rd iop.ADDI)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- mvcgen composes liftSail_ADDI_spec + vsew_spec to characterize the Jolt result.
theorem jolt_addiw_concrete (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      (jolt_addiw imm rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v1 + sign_extend (m := 64) imm) 31 0)) := by
  unfold jolt_addiw
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  · -- VC: hrd_ok — rd is readable after the ADDI write
    rename_i r1 s1 h_addi
    obtain ⟨rfl, v1, h_rx1, h_proj1⟩ := h_addi
    rw [h_proj1]
    exact ⟨v1 + sign_extend (m := 64) imm,
           rX_after_stateAfterWrite rd _ js.sail hrd⟩
  · -- Main VC: connect the results
    rename_i r1 s1 h_addi r2 s2 h_vsew
    obtain ⟨rfl, v1, h_rx1, h_proj1⟩ := h_addi
    obtain ⟨v, h_rxrd, h_proj2⟩ := h_vsew
    refine ⟨s2, v1, h_rx1, rfl, ?_⟩
    rw [h_proj2, h_proj1, stateAfterWrite_stateAfterWrite]
    rw [h_proj1] at h_rxrd
    rw [rX_after_stateAfterWrite rd _ js.sail hrd] at h_rxrd
    have h_v : v = v1 + sign_extend (m := 64) imm :=
      (EStateM.Result.ok.inj h_rxrd).1.symm
    rw [h_v]

-- ============================================================================
-- Main theorem: Jolt ADDIW = Sail ADDIW
-- ============================================================================

-- Running Jolt's ADDIW decomposition (ADDI + VSEW) and projecting onto Sail state
-- produces exactly the same result as running Sail's native ADDIW instruction.
-- The math is trivial: both sides compute sign_extend(extractLsb(v1 + sign_extend(imm))).
theorem jolt_addiw_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_addiw imm rs1 rd).run js) =
    (execute_ADDIW imm rs1 rd).run js.sail := by
  obtain ⟨js', v1, hj_rx1, hj, hj_sail⟩ :=
    jolt_addiw_concrete imm rs1 rd hrd js hwf
  -- Sail side: unfold and rewrite with the same v1
  simp only [execute_ADDIW, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1]
  -- Jolt side: rewrite with concrete result
  show projectResult ((jolt_addiw imm rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  -- Both sides write sign_extend(extractLsb(v1 + sign_extend(imm))) — same value.
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
