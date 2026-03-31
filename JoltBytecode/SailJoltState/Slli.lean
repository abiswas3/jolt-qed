import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLI: Jolt decomposition = Sail SLLI

SLLI is a single-step instruction (no VirtualSignExtendWord needed).
Jolt decomposes it via VirtualMULI (multiply by 2^shift), but at the
SailM level we just lift execute_SHIFTIOP directly.

The Jolt decomposition at the pure level uses multiplication by 2^shift,
but the Sail execute_SHIFTIOP uses shift_bits_left. These are equal
(shifting left by n = multiplying by 2^n for bitvectors).
-/

-- Jolt's SLLI: just lift the Sail instruction (no decomposition needed).
def jolt_slli (shamt : BitVec 6) (rs1 rd : regidx) : JoltMonad ExecutionResult :=
  liftSail (execute_SHIFTIOP shamt rs1 rd sop.SLLI)

-- Main theorem: trivial since jolt_slli IS liftSail of the Sail instruction.
-- liftSail_project gives us this for free.
theorem jolt_slli_eq_sail (shamt : BitVec 6) (rs1 rd : regidx) (js : JoltState) :
    projectResult ((jolt_slli shamt rs1 rd).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run (project js) := by
  exact liftSail_project (execute_SHIFTIOP shamt rs1 rd sop.SLLI) js

end
