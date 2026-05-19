import JoltBytecode.JoltISA.Semantics

/-!
# System-instruction Jolt expansion programs

These are literal transcriptions of the Rust expansion layer in
`crates/jolt-program/src/expand/control_flow/{ecall,ebreak}.rs`.

The reserved virtual registers follow `ExpansionAllocator`:

* `v34`: trap handler / `mtvec`
* `v36`: `mepc`
* `v37`: `mcause`
* `v38`: `mtval`
* `v39`: `mstatus`
* `v40`: first scratch register allocated for an instruction expansion
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

def trapHandlerVReg : VReg := 34
def mepcVReg : VReg := 36
def mcauseVReg : VReg := 37
def mtvalVReg : VReg := 38
def mstatusVReg : VReg := 39
def systemScratchVReg : VReg := 40

/-- Rust `expand_ecall`: materialize virtual trap CSRs and jump to `mtvec`. -/
def ecallProgram : Program :=
  .instr (.AUIPC (.vreg systemScratchVReg) (0 : BitVec 20)) <|
  .instr (.ADDI (.vreg mepcVReg) (.vreg systemScratchVReg) (0 : BitVec 12)) <|
  .instr (.ADDI (.vreg mcauseVReg) (.xreg (regidx.Regidx 0)) (11 : BitVec 12)) <|
  .instr (.ADDI (.vreg mtvalVReg) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  .instr (.ADDI (.vreg systemScratchVReg) (.xreg (regidx.Regidx 0)) (3 : BitVec 12)) <|
  .instr (.VirtualMULI (.vreg mstatusVReg) (.vreg systemScratchVReg) (2048 : BitVec 64)) <|
  .instr (.JALR (.vreg systemScratchVReg) (.vreg trapHandlerVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Rust `expand_ebreak`: emit `JAL scratch, 0`, a self-loop termination marker. -/
def ebreakProgram : Program :=
  .instr (.JAL (.vreg systemScratchVReg) (0 : BitVec 21)) <|
  .done RETIRE_SUCCESS

end JoltISA
