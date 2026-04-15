import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srai

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# Advice Helpers

Shared infrastructure for the tracer's `AdviceLB/LH/LW/LD` instructions.

These instructions read a host-provided, read-only advice value. In the
embedded model we treat that value as an explicit input and keep the reusable
execution facts here:

* `VirtualAdviceLoad`
* the common `SLLI` / `SRAI` step lemmas
* the generic collapse theorem from the inline sequence to the compact spec
* the generic `projectResult` lifting lemmas
-/

/-- Embedded model of `VirtualAdviceLoad`: write the zero-extended advice value to `rd`. -/
def jolt_virtual_advice_load (rd : regidx) (value : BitVec 64) : JoltMonad Unit := do
  liftSail (wX_bits rd value)

lemma sshiftRight_slli_signExtend_8 (x : BitVec 8) :
    (x.setWidth 64 <<< 56).sshiftRight 56 = x.signExtend 64 := by
  bv_decide

lemma sshiftRight_slli_signExtend_16 (x : BitVec 16) :
    (x.setWidth 64 <<< 48).sshiftRight 48 = x.signExtend 64 := by
  bv_decide

lemma sshiftRight_slli_signExtend_32 (x : BitVec 32) :
    (x.setWidth 64 <<< 32).sshiftRight 32 = x.signExtend 64 := by
  bv_decide

theorem execute_SHIFTIOP_SLLI_eq_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, bind_pure_comp]

private theorem execute_advice_slli_step_nonzero
    (rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (val : BitVec 64) (shamt : BitVec 6) (tail : SailM ExecutionResult) :
    (do
      wX_bits rd val
      let _ ← execute_SHIFTIOP shamt rd rd sop.SLLI
      tail : SailM ExecutionResult) =
    (do
      wX_bits rd (shift_bits_left val shamt)
      tail : SailM ExecutionResult) := by
  funext s
  simp only [bind, EStateM.bind]
  obtain ⟨s1, hw1⟩ := wX_shape rd val s
  rw [hw1]
  have hs1 : s1 = stateAfterWrite s rd val := by
    exact wX_bits_eq_stateAfterWrite rd val s s1 hw1
  rw [hs1]
  simp only
  have hslli :
      execute_SHIFTIOP shamt rd rd sop.SLLI (stateAfterWrite s rd val) =
        .ok RETIRE_SUCCESS (stateAfterWrite s rd (shift_bits_left val shamt)) := by
    rw [execute_SHIFTIOP_SLLI_eq_factored]
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    rw [rX_after_stateAfterWrite rd val s hrd]
    simp only
    obtain ⟨s', hw⟩ := wX_shape rd
      (shift_bits_left val
        (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0))
      (stateAfterWrite s rd val)
    rw [hw]
    have hs' : s' = stateAfterWrite (stateAfterWrite s rd val) rd
        (shift_bits_left val
          (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)) := by
      exact wX_bits_eq_stateAfterWrite rd _ _ s' hw
    rw [hs', stateAfterWrite_stateAfterWrite]
    have hshamt :
        Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
      simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
      ext i
      simp
      change shamt.getLsbD i = shamt.getLsbD i
      rfl
    rw [hshamt]
    rfl
  rw [hslli]
  obtain ⟨s2, hw2⟩ := wX_shape rd (shift_bits_left val shamt) s
  rw [hw2]
  have hs2 : s2 = stateAfterWrite s rd (shift_bits_left val shamt) := by
    exact wX_bits_eq_stateAfterWrite rd _ s s2 hw2
  rw [hs2]

private theorem execute_SHIFTIOP_SRAI_run_after_write
    (rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (val : BitVec 64) (shamt : BitVec 6) (s : SailState) :
    (execute_SHIFTIOP shamt rd rd sop.SRAI).run (stateAfterWrite s rd val) =
      .ok RETIRE_SUCCESS (stateAfterWrite s rd (shift_bits_right_arith val shamt)) := by
  rw [execute_SHIFTIOP_SRAI_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  rw [rX_after_stateAfterWrite rd val s hrd]
  simp only
  obtain ⟨s', hw⟩ := wX_shape rd (shift_bits_right_arith val (Sail.BitVec.extractLsb shamt 5 0))
    (stateAfterWrite s rd val)
  rw [hw]
  have hs' : s' = stateAfterWrite (stateAfterWrite s rd val) rd
      (shift_bits_right_arith val (Sail.BitVec.extractLsb shamt 5 0)) := by
    exact wX_bits_eq_stateAfterWrite rd _ _ s' hw
  rw [hs', stateAfterWrite_stateAfterWrite]
  have hshamt : Sail.BitVec.extractLsb shamt 5 0 = shamt := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, shamt.isLt]
  rw [hshamt]

private theorem execute_advice_srai_step_nonzero
    (rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (val : BitVec 64) (shamt : BitVec 6) (tail : SailM ExecutionResult) :
    (do
      wX_bits rd val
      let _ ← execute_SHIFTIOP shamt rd rd sop.SRAI
      tail : SailM ExecutionResult) =
    (do
      wX_bits rd (shift_bits_right_arith val shamt)
      tail : SailM ExecutionResult) := by
  funext s
  simp only [bind, EStateM.bind]
  obtain ⟨s1, hw1⟩ := wX_shape rd val s
  rw [hw1]
  have hs1 : s1 = stateAfterWrite s rd val := by
    exact wX_bits_eq_stateAfterWrite rd val s s1 hw1
  rw [hs1]
  simp only
  have hsrai :
      execute_SHIFTIOP shamt rd rd sop.SRAI (stateAfterWrite s rd val) =
        .ok RETIRE_SUCCESS (stateAfterWrite s rd (shift_bits_right_arith val shamt)) := by
    simpa using execute_SHIFTIOP_SRAI_run_after_write rd hrd val shamt s
  rw [hsrai]
  obtain ⟨s2, hw2⟩ := wX_shape rd (shift_bits_right_arith val shamt) s
  rw [hw2]
  have hs2 : s2 = stateAfterWrite s rd (shift_bits_right_arith val shamt) := by
    exact wX_bits_eq_stateAfterWrite rd _ s s2 hw2
  rw [hs2]

/-- Shared advice collapse theorem for the RV64 sign-extending inline shape. -/
theorem execute_advice_inline_eq_spec_nonzero
    (rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (val final : BitVec 64) (shamt : BitVec 6)
    (hfinal : shift_bits_right_arith (shift_bits_left val shamt) shamt = final) :
    (do
      wX_bits rd val
      let _ ← execute_SHIFTIOP shamt rd rd sop.SLLI
      let _ ← execute_SHIFTIOP shamt rd rd sop.SRAI
      pure RETIRE_SUCCESS : SailM ExecutionResult) =
    (do
      wX_bits rd final
      pure RETIRE_SUCCESS : SailM ExecutionResult) := by
  calc
    (do
      wX_bits rd val
      let _ ← execute_SHIFTIOP shamt rd rd sop.SLLI
      let _ ← execute_SHIFTIOP shamt rd rd sop.SRAI
      pure RETIRE_SUCCESS : SailM ExecutionResult)
      =
    (do
      wX_bits rd (shift_bits_left val shamt)
      let _ ← execute_SHIFTIOP shamt rd rd sop.SRAI
      pure RETIRE_SUCCESS : SailM ExecutionResult) := by
        simpa using execute_advice_slli_step_nonzero rd hrd val shamt
          (do
            let _ ← execute_SHIFTIOP shamt rd rd sop.SRAI
            pure RETIRE_SUCCESS : SailM ExecutionResult)
    _ =
    (do
      wX_bits rd (shift_bits_right_arith (shift_bits_left val shamt) shamt)
      pure RETIRE_SUCCESS : SailM ExecutionResult) := by
        simpa using execute_advice_srai_step_nonzero rd hrd (shift_bits_left val shamt) shamt
          (pure RETIRE_SUCCESS : SailM ExecutionResult)
    _ = (do
      wX_bits rd final
      pure RETIRE_SUCCESS : SailM ExecutionResult) := by
        simp [hfinal]

theorem projectResult_liftSail_seq1
    (m : SailM Unit) (js : SailJoltState) :
    projectResult
      ((do
          let _ ← liftSail m
          pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js) =
      (do
        let _ ← m
        pure RETIRE_SUCCESS : SailM ExecutionResult).run js.sail := by
  cases h : m js.sail <;>
    simp [liftSail, projectResult, project, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, h]

theorem projectResult_liftSail_seq3
    (m1 : SailM Unit) (m2 m3 : SailM ExecutionResult) (js : SailJoltState) :
    projectResult
      ((do
          let _ ← liftSail m1
          let _ ← liftSail m2
          let _ ← liftSail m3
          pure RETIRE_SUCCESS : JoltMonad ExecutionResult).run js) =
      (do
        let _ ← m1
        let _ ← m2
        let _ ← m3
        pure RETIRE_SUCCESS : SailM ExecutionResult).run js.sail := by
  cases h1 : m1 js.sail with
  | error e s =>
      simp [liftSail, projectResult, project, EStateM.run, bind, EStateM.bind, h1]
  | ok _ s =>
      cases h2 : m2 s with
      | error e s' =>
          simp [liftSail, projectResult, project, EStateM.run, bind, EStateM.bind, pure, h1, h2]
      | ok _ s' =>
          cases h3 : m3 s' with
          | error e s'' =>
              simp [liftSail, projectResult, project, EStateM.run, bind, EStateM.bind, pure, h1, h2, h3]
          | ok _ s'' =>
              simp [liftSail, projectResult, project, EStateM.run, bind, EStateM.bind, pure, EStateM.pure, h1, h2, h3]

end
