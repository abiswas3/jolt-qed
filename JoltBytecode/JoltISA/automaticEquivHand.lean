import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.Expansions.Advice
import JoltBytecode.JoltISA.ExpansionsAutomated

/-!
# Hand-written vs auto-generated expansion equivalence

Each theorem shows a hand-written `…Program` (in `JoltISA/Expansions/`) equals
the auto-generated `…ProgramAuto` (in `JoltISA/ExpansionsAutomated.lean`,
produced by `jolt-lean-gen --lean`). The argument order differs between the two
(hand: `rs2 rs1 rd`; auto: `rd rs1 rs2`).

-/

open Sail PreSail LeanRV64D.Functions

set_option linter.unusedSimpArgs false

namespace JoltISA

/-! ## Advice loads -/

theorem advicelb_auto_eq (rd : regidx) (advice : BitVec 8) :
    advicelbProgram rd advice = advicelbProgramAuto rd (advice.setWidth 64) := by
  unfold advicelbProgram advicelbProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem advicelh_auto_eq (rd : regidx) (advice : BitVec 16) :
    advicelhProgram rd advice = advicelhProgramAuto rd (advice.setWidth 64) := by
  unfold advicelhProgram advicelhProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem advicelw_auto_eq (rd : regidx) (advice : BitVec 32) :
    advicelwProgram rd advice = advicelwProgramAuto rd (advice.setWidth 64) := by
  unfold advicelwProgram advicelwProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem adviceld_auto_eq (rd : regidx) (advice : BitVec 64) :
    adviceldProgram rd advice = adviceldProgramAuto rd advice := by
  unfold adviceldProgram adviceldProgramAuto adviceLoadDstFor sideEffectingRdZeroDst
    rdZeroRewriteVReg
  cases isX0 rd <;> rfl

end JoltISA
