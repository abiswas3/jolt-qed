import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-! ## MULW: Jolt MUL + VSEW = Sail MULW

Jolt decomposes MULW as:
1. MUL rd, rs1, rs2 — 64-bit multiply
2. VirtualSignExtendWord rd — sign-extend lower 32 bits
-/

-- Factoring: execute_MULW reads rs1, rs2, multiplies lower 32 bits as ints,
-- truncates to 32, sign-extends to 64.
private theorem execute_MULW_factored (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1; let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32)
        (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
         BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      pure RETIRE_SUCCESS) := by
  simp [execute_MULW, bind_pure_comp, pure_bind]

-- Bridge: Jolt's 64-bit multiply truncated to 32 = Sail's MULW computation
private lemma mulw_bridge (v1 v2 : BitVec 64) :
    Sail.BitVec.extractLsb (v1 * v2) 31 0 =
    to_bits_truncate (l := 32)
      (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
       BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)) := by
  sorry

-- Jolt's MULW: 64-bit multiply then sign-extend lower 32 bits.
def jolt_mulw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1 * v2))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

-- Concrete: Jolt writes sign_extend(to_bits_truncate(toInt(v1[31:0]) * toInt(v2[31:0]))) to rd.
theorem jolt_mulw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64) (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))) := by
  sorry

-- Running Jolt's MULW and projecting equals running Sail's MULW.
theorem jolt_mulw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulw rs2 rs1 rd).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail := by
  obtain ⟨js', v1, v2, hj_rx1, hj_rx2, hj, hj_sail⟩ :=
    jolt_mulw_concrete rs2 rs1 rd hrd js hwf
  rw [execute_MULW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hj_rx1, hj_rx2]
  show projectResult ((jolt_mulw rs2 rs1 rd).run js) = _
  rw [hj]
  simp only [projectResult, project]
  rw [hj_sail]
  obtain ⟨s', hw⟩ := wX_shape rd _ js.sail
  rw [hw]
  congr 1
  exact (wX_bits_eq_stateAfterWrite rd _ js.sail s' hw).symm

end
