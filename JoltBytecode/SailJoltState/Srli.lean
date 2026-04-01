import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLI: Jolt decomposition = Sail SRLI

SRLI is a single-step instruction — just lift execute_SHIFTIOP directly.
-/

def jolt_srli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  liftSail (execute_SHIFTIOP shamt rs1 rd sop.SRLI)

theorem jolt_srli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx) (js : SailJoltState) :
    projectResult ((jolt_srli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SRLI).run (project js) :=
  liftSail_project (execute_SHIFTIOP shamt rs1 rd sop.SRLI) js

end
