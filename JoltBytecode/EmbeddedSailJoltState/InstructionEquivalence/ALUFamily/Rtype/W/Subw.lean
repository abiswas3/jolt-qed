import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Sub

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SUBW: Jolt SUB + VirtualSignExtendWord = Sail SUBW

Identical in shape to `ADDW`; the only differences are the operation
(`rop.SUB` / `ropw.SUBW`) and the bridge (`extractLsb_sub`).
-/

theorem execute_RTYPE_SUB_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SUB = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 - v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp, pure_bind]

theorem execute_RTYPEW_SUBW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.SUBW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

def jolt_subw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.SUB)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_subw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_subw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0)) := by
  obtain ⟨js', v1, v2, h1, h2, h3, h4⟩ :=
    jolt_rtype_w_concrete rop.SUB (· - ·) execute_RTYPE_SUB_factored rs2 rs1 rd hrd js hwf
  refine ⟨js', v1, v2, h1, h2, h3, ?_⟩
  rw [← extractLsb_sub v1 v2]
  exact h4

theorem jolt_subw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_subw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SUBW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (Sail.BitVec.extractLsb v1 31 0 - Sail.BitVec.extractLsb v2 31 0))
    (execute_RTYPEW_SUBW_factored rs2 rs1 rd)
    (jolt_subw_concrete rs2 rs1 rd hrd js hwf)

end
