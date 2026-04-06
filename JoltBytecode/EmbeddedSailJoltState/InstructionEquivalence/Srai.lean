import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.BytecodeExpansions.Instructions.Srai

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# SRAI: Jolt VirtualSRAI via bitmask = Sail SRAI

Jolt has no native SRAI instruction. Instead it precomputes a bitmask
from the shift amount and uses VirtualSRAI, which performs arithmetic
right shift by ctz(bitmask) bits.

The key identity (from BytecodeExpansions): ctz(bitmask) = shamt,
so the bitmask roundtrip recovers the original shift amount.

Unlike the W-type instructions, SRAI has no VSEW step — it directly
reads, shifts, and writes.
-/

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- Jolt computes sshiftRight(v, ctz(bitmask)). Sail computes
-- shift_bits_right_arith(v, extractLsb(shamt)). These are equal because
-- ctz(bitmask) = shamt (proved in BytecodeExpansions).
lemma srai_bitmask_eq_arith_shift (v : BitVec 64) (shamt : BitVec 6) :
    v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64))) =
    shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0) := by
  unfold shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, Sail.BitVec.extractLsb, ctz_srai_bitmask]
  congr 1; omega

-- ============================================================================
-- Factoring
-- ============================================================================

-- The Sail execute_SHIFTIOP for SRAI reads rs1, arithmetically right-shifts
-- by the shift amount, and writes the result to rd.
theorem execute_SHIFTIOP_SRAI_eq_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SRAI = (do
      let v ← rX_bits rs1
      wX_bits rd (shift_bits_right_arith v (Sail.BitVec.extractLsb shamt 5 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_SHIFTIOP, LeanRV64D.Functions.log2_xlen]

-- ============================================================================
-- Jolt SRAI definition and mvcgen composition
-- ============================================================================

-- Jolt's SRAI decomposition: read rs1, arithmetic right shift by ctz(bitmask),
-- write to rd. The bitmask is precomputed from the shift amount.
def jolt_srai (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v ← liftSail (rX_bits rs1)
  liftSail (wX_bits rd (v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64)))))
  pure RETIRE_SUCCESS

-- mvcgen composes liftSail_rX_spec + liftSail_wX_spec to characterize the
-- Jolt result. The primitive specs handle the monadic plumbing automatically.
theorem jolt_srai_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v : BitVec 64),
      rX_bits rs1 js.sail = .ok v js.sail ∧
      (jolt_srai shamt rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (v.sshiftRight (ctz (srai_bitmask (shamt.setWidth 64)))) := by
  unfold jolt_srai
  generalize hrun : EStateM.run _ js = x
  apply EStateM.of_wp_run_eq hrun
  mvcgen
  -- Single VC: connect the read and write results
  rename_i v js1 h_read _ js2 h_write
  obtain ⟨h_rx, rfl⟩ := h_read
  obtain ⟨h_sail, _⟩ := h_write
  exact ⟨js2, v, h_rx, rfl, h_sail⟩

-- ============================================================================
-- Main theorem: Jolt SRAI = Sail SRAI
-- ============================================================================

-- Running Jolt's SRAI (VirtualSRAI via bitmask) and projecting onto Sail state
-- produces exactly the same result as running Sail's native SRAI instruction.
-- The bridge is srai_bitmask_eq_arith_shift: ctz(bitmask) recovers the shift amount.
theorem jolt_srai_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_srai shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRAI).run js.sail := by
  obtain ⟨js', v, hj_rx, hj, hj_sail⟩ :=
    jolt_srai_concrete shamt rs1 rd js hwf
  -- Sail side: unfold and rewrite with the same v
  rw [execute_SHIFTIOP_SRAI_eq_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx]
  -- Jolt side: rewrite with concrete result
  show projectResult ((jolt_srai shamt rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  -- Bridge: Jolt's sshiftRight via ctz(bitmask) = Sail's shift_bits_right_arith
  rw [srai_bitmask_eq_arith_shift]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
