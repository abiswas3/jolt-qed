import JoltBytecode.JoltISA.Expansions.ALU

/-!
# Advice-family Jolt expansion programs

These are the final-row Jolt-ISA programs for the tracer's advice-load source
instructions. The advice value itself is explicit in the formal model; Rust's
byte tape is an implementation-conformance layer outside these definitions.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust source-materialization rule for side-effecting advice-load
instructions with `rd = x0`: keep the advice-load row, but redirect the
destination to the first instruction-local temporary. -/
def adviceLoadDstFor (rd : regidx) : Dst :=
  sideEffectingRdZeroDst rd

/-- Source form of `adviceLoadDstFor`, for the following sign-extension rows
that read back the advice-loaded value. -/
def adviceLoadSrcFor (rd : regidx) : Src :=
  if isX0 rd then .vreg rdZeroRewriteVReg else .xreg rd

/-- Rust's RV64 `AdviceLB::inline_sequence`: load the advised byte, then
sign-extend it with the lowered `SLLI 56; SRAI 56` sequence. -/
def advicelbProgram (rd : regidx) (advice : BitVec 8) : Program :=
  let dst := adviceLoadDstFor rd
  let src := adviceLoadSrcFor rd
  .instr (.VirtualAdviceLoad dst (advice.setWidth 64)) <|
  slliBlock dst src (56 : BitVec 6) <|
  .instr (.VirtualSRAI dst src (sraiBitmask (56 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLH::inline_sequence`: load the advised halfword, then
sign-extend it with the lowered `SLLI 48; SRAI 48` sequence. -/
def advicelhProgram (rd : regidx) (advice : BitVec 16) : Program :=
  let dst := adviceLoadDstFor rd
  let src := adviceLoadSrcFor rd
  .instr (.VirtualAdviceLoad dst (advice.setWidth 64)) <|
  slliBlock dst src (48 : BitVec 6) <|
  .instr (.VirtualSRAI dst src (sraiBitmask (48 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLW::inline_sequence`: load the advised word, then
sign-extend it with the lowered `SLLI 32; SRAI 32` sequence. -/
def advicelwProgram (rd : regidx) (advice : BitVec 32) : Program :=
  let dst := adviceLoadDstFor rd
  let src := adviceLoadSrcFor rd
  .instr (.VirtualAdviceLoad dst (advice.setWidth 64)) <|
  slliBlock dst src (32 : BitVec 6) <|
  .instr (.VirtualSRAI dst src (sraiBitmask (32 : BitVec 6))) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLD::inline_sequence`: load the advised doubleword. -/
def adviceldProgram (rd : regidx) (advice : BitVec 64) : Program :=
  .instr (.VirtualAdviceLoad (adviceLoadDstFor rd) advice) <|
  .done RETIRE_SUCCESS

end JoltISA
