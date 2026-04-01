import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLI: Jolt decomposition = Sail SLLI

SLLI is a single-step instruction — just lift execute_SHIFTIOP directly.
No VirtualSignExtendWord needed.
-/

def jolt_slli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  liftSail (execute_SHIFTIOP shamt rs1 rd sop.SLLI)

theorem jolt_slli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx) (js : SailJoltState) :
    projectResult ((jolt_slli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run (project js) :=
  liftSail_project (execute_SHIFTIOP shamt rs1 rd sop.SLLI) js

end
