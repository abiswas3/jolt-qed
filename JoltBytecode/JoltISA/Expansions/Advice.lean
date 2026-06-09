import JoltBytecode.JoltISA.Expansions.ALU

/-!
# Advice-family Jolt expansion programs

These are the final-row Jolt-ISA programs for the tracer's advice-load source
instructions. The advice value itself is explicit in the formal model; Rust's
byte tape is an implementation-conformance layer outside these definitions.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's RV64 `AdviceLB::inline_sequence`: load the advised byte, then
sign-extend it with the lowered `SLLI 56; SRAI 56` sequence. -/
def advicelbProgram (rd : regidx) (advice : BitVec 8) : Program :=
  pureWritebackTraceProgram rd <|
    .instr (.VirtualAdviceLoad (.xreg rd) (advice.setWidth 64)) <|
    slliBlock (.xreg rd) (.xreg rd) (56 : BitVec 6) <|
    .instr (.VirtualSRAI (.xreg rd) (.xreg rd) (sraiBitmask (56 : BitVec 6))) <|
    .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLH::inline_sequence`: load the advised halfword, then
sign-extend it with the lowered `SLLI 48; SRAI 48` sequence. -/
def advicelhProgram (rd : regidx) (advice : BitVec 16) : Program :=
  pureWritebackTraceProgram rd <|
    .instr (.VirtualAdviceLoad (.xreg rd) (advice.setWidth 64)) <|
    slliBlock (.xreg rd) (.xreg rd) (48 : BitVec 6) <|
    .instr (.VirtualSRAI (.xreg rd) (.xreg rd) (sraiBitmask (48 : BitVec 6))) <|
    .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLW::inline_sequence`: load the advised word, then
sign-extend it with the lowered `SLLI 32; SRAI 32` sequence. -/
def advicelwProgram (rd : regidx) (advice : BitVec 32) : Program :=
  pureWritebackTraceProgram rd <|
    .instr (.VirtualAdviceLoad (.xreg rd) (advice.setWidth 64)) <|
    slliBlock (.xreg rd) (.xreg rd) (32 : BitVec 6) <|
    .instr (.VirtualSRAI (.xreg rd) (.xreg rd) (sraiBitmask (32 : BitVec 6))) <|
    .done RETIRE_SUCCESS

/-- Rust's RV64 `AdviceLD::inline_sequence`: load the advised doubleword. -/
def adviceldProgram (rd : regidx) (advice : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
    .instr (.VirtualAdviceLoad (.xreg rd) advice) <|
    .done RETIRE_SUCCESS

end JoltISA
