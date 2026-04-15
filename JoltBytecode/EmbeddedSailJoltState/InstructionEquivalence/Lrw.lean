import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# LRW: Jolt load-reserved word decomposition

From `tracer/src/instruction/lrw.rs::inline_sequence_64`:

    ADDI vr32, rs1, 0   -- reservation_w
    ADDI vr33, x0, 0    -- clear reservation_d
    LW   rd, rs1, 0
-/

def jolt_lrw (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let rs1_val ← liftSail (rX_bits rs1)
  writeVReg (32 : BitVec 7) rs1_val
  writeVReg (33 : BitVec 7) 0
  liftSail (execute_LOAD (0 : BitVec 12) rs1 rd false 4)

