import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Add

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# ADDW: Jolt ADD + VirtualSignExtendWord = Sail ADDW

Jolt decomposes ADDW as:
1. `execute_RTYPE rop.ADD` — 64-bit add, writes `v1 + v2` to `rd`
2. `VirtualSignExtendWord rd` — sign-extend lower 32 bits of `rd`

Sail's ADDW extracts lower 32 bits of each operand, adds them at 32
bits, and sign-extends to 64. The bridge lemma `extractLsb_add` (imported
from `ALUFamily/Bridges/Add.lean`) says truncation distributes over
addition, so both sides produce the same result.
-/

/-- Factoring: `execute_RTYPE rs2 rs1 rd rop.ADD` reads `rs1`, reads
`rs2`, writes `v1 + v2` to `rd`, returns `RETIRE_SUCCESS`. -/
theorem execute_RTYPE_ADD_factored (rs2 rs1 rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.ADD = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (v1 + v2)
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPE, bind_pure_comp]

/-- Factoring: `execute_RTYPEW rs2 rs1 rd ropw.ADDW` reads `rs1`, reads
`rs2`, writes `sext₆₄(v1[31:0] +₃₂ v2[31:0])` to `rd`, returns
`RETIRE_SUCCESS`. -/
theorem execute_RTYPEW_ADDW_factored (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      pure RETIRE_SUCCESS) := by
  simp [execute_RTYPEW, bind_pure_comp, pure_bind]

/-- Jolt's ADDW: 64-bit `ADD` followed by virtual sign-extend-word. -/
def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

/-- After running `jolt_addw`, register `rd` holds
`sext₆₄(v1[31:0] + v2[31:0])`, where `v1`, `v2` are the values read from
`rs1`, `rs2` on the Sail side. -/
theorem jolt_addw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_addw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) := by
  obtain ⟨js', v1, v2, h1, h2, h3, h4⟩ :=
    jolt_rtype_w_concrete rop.ADD (· + ·) execute_RTYPE_ADD_factored rs2 rs1 rd hrd js hwf
  refine ⟨js', v1, v2, h1, h2, h3, ?_⟩
  rw [← extractLsb_add v1 v2]
  exact h4

/-- Main equivalence: running Jolt's ADDW decomposition and projecting
onto the Sail state yields the same result as running Sail's native
`ADDW` on the initial Sail state. -/
theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
    (execute_RTYPEW_ADDW_factored rs2 rs1 rd)
    (jolt_addw_concrete rs2 rs1 rd hrd js hwf)

end
