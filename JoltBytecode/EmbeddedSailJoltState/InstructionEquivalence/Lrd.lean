import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do

set_option autoImplicit true

noncomputable section

/-!
# LRD: Jolt load-reserved dword decomposition

From `tracer/src/instruction/lrd.rs::inline_sequence_64`:

    ADDI vr33, rs1, 0   -- reservation_d
    ADDI vr32, x0, 0    -- clear reservation_w
    LD   rd, rs1, 0
-/

def jolt_lrd (rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let rs1_val ← liftSail (rX_bits rs1)
  writeVReg (33 : BitVec 7) rs1_val
  writeVReg (32 : BitVec 7) 0
  liftSail (execute_LOAD (0 : BitVec 12) rs1 rd false 8)

