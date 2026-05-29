import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# System-instruction Jolt expansion programs

These are literal transcriptions of the Rust `inline_sequence` implementations
in `tracer/src/instruction/{ecall,ebreak}.rs`.

The reserved virtual registers follow `tracer/src/utils/virtual_registers.rs`:

* `v34`: trap handler / `mtvec`
* `v36`: `mepc`
* `v37`: `mcause`
* `v38`: `mtval`
* `v39`: `mstatus`
* `v40`: first scratch register allocated for an instruction expansion
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's first `allocate()` result for system expansions. -/
def systemScratchVReg : VReg := inlineTmp0

/-- Rust `expand_ecall`: materialize virtual trap CSRs and jump to `mtvec`. -/
def ecallProgram : Program :=
  -- Rust: `AUIPC ecall_addr, 0`.
  -- Jolt: `ecall_addr` is the first instruction-local scratch register, v40.
  .instr (.AUIPC (.vreg systemScratchVReg) (0 : BitVec 20)) <|
  -- Rust: `ADDI mepc, ecall_addr, 0`.
  -- Jolt: write the current PC into the virtual `mepc` CSR, v36.
  .instr (.ADDI (.vreg mepcVReg) (.vreg systemScratchVReg) (0 : BitVec 12)) <|
  -- Rust: `ADDI mcause, x0, MCAUSE_ECALL_FROM_MMODE`.
  -- Jolt: write machine-mode ECALL cause 11 into virtual `mcause`, v37.
  .instr (.ADDI (.vreg mcauseVReg) (.xreg (regidx.Regidx 0)) (11 : BitVec 12)) <|
  -- Rust: `ADDI mtval, x0, 0`.
  -- Jolt: machine-mode ECALL has no trap value, so virtual `mtval`, v38, is 0.
  .instr (.ADDI (.vreg mtvalVReg) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  -- Rust: `ADDI three, x0, 3`.
  -- Jolt: reuse v40 after `ecall_addr` is dropped.
  .instr (.ADDI (.vreg systemScratchVReg) (.xreg (regidx.Regidx 0)) (3 : BitVec 12)) <|
  -- Rust source row: `SLLI mstatus, three, 11`.
  -- Jolt final row: `SLLI` lowers to `VirtualMULI` by `2^11 = 2048`.
  .instr (.VirtualMULI (.vreg mstatusVReg) (.vreg systemScratchVReg) (2048 : BitVec 64)) <|
  -- Rust: `JALR jalr_rd, trap_handler, 0`.
  -- Jolt: jump through virtual `mtvec`, v34, and discard the link in v40.
  .instr (.JALR (.vreg systemScratchVReg) (.vreg trapHandlerVReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Rust `expand_ebreak`: emit `JAL scratch, 0`, a self-loop termination marker. -/
def ebreakProgram : Program :=
  .instr (.JAL (.vreg systemScratchVReg) (0 : BitVec 21)) <|
  .done RETIRE_SUCCESS

end JoltISA
