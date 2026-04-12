import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# SUBW: Jolt SUB + VirtualSignExtendWord = Sail SUBW

Jolt decomposes SUBW as:
1. execute_RTYPE SUB rd, rs1, rs2  — 64-bit subtract
2. VirtualSignExtendWord rd        — sign-extend lower 32 bits of rd

Sail's SUBW extracts lower 32 bits of each operand, subtracts them (32-bit),
sign-extends to 64. The bridge lemma shows truncation distributes over
subtraction, so both sides produce the same result.
-/

-- ============================================================================
-- Factoring lemmas
-- ============================================================================

-- Factoring: execute_RTYPE SUB reads rs1, rs2, writes v1 - v2.
theorem execute_RTYPE_SUB_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (v1 - v2); pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp, pure_bind]

-- Factoring: execute_RTYPEW SUBW reads rs1, rs2, truncates to 32, subtracts, sign-extends.
theorem execute_RTYPEW_SUBW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

-- ============================================================================
-- Bridge lemma
-- ============================================================================

-- Truncating to 32 bits distributes over subtraction.
-- extractLsb(a - b, 31, 0) = extractLsb(a, 31, 0) - extractLsb(b, 31, 0)
--
-- This is the mathematical core: Jolt computes v1 - v2 at 64 bits then
-- truncates, while Sail truncates then subtracts. Both give the same 32-bit
-- result because subtraction mod 2^32 doesn't depend on upper bits.
theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

-- ============================================================================
-- Jolt SUBW definition
-- ============================================================================

-- Jolt's SUBW decomposition: 64-bit SUB then sign-extend lower 32 bits.
def jolt_subw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- ============================================================================
-- Concrete characterization (mvcgen)
-- ============================================================================

-- After running Jolt's SUBW, rd holds sign_extend(extractLsb(v1) - extractLsb(v2)).
theorem jolt_subw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_subw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)) := by
  have h := jolt_rtype_w_concrete rop.SUB (· - ·) execute_RTYPE_SUB_factored rs2 rs1 rd hrd js hwf
  obtain ⟨js', v1, v2, h1, h2, h3, h4⟩ := h
  refine ⟨js', v1, v2, h1, h2, h3, ?_⟩
  rw [← extractLsb_sub v1 v2]
  exact h4

-- ============================================================================
-- Main theorem: Jolt SUBW = Sail SUBW
-- ============================================================================

-- Running Jolt's SUBW decomposition (SUB + VSEW) and projecting onto Sail state
-- produces exactly the same result as running Sail's native SUBW instruction.
theorem jolt_subw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_subw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_subw_concrete rs2 rs1 rd hrd js hwf
  -- Sail side: unfold and rewrite with the same v1, v2
  rw [execute_RTYPEW_SUBW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  -- Jolt side: rewrite with concrete result
  show projectResult ((jolt_subw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  -- Both sides now write the same value.
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
