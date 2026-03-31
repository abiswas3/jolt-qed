import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRAI: Jolt decomposition = Sail SRAI

SRAI is a single-step instruction (no sign-extend needed).
Same pattern as SLLI/SRLI — just lift execute_SHIFTIOP directly.
-/

def jolt_srai (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  liftSail (execute_SHIFTIOP shamt rs1 rd sop.SRAI)

theorem jolt_srai_eq_sail (shamt : BitVec 6) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_srai shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRAI).run (project js) := by
  simp only [jolt_srai, liftSail, projectResult, project, EStateM.run]
  cases execute_SHIFTIOP shamt rs1 rd sop.SRAI
      ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ <;> simp

end
