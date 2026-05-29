import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# M-extension Jolt expansion programs

These definitions are data, not proofs.  They are intentionally close to the
Rust inline sequences and are the shape a future Rust-to-Lean extractor should
produce.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's `MULH::inline_sequence` as a reusable block.

The caller supplies the three scratch virtual registers from the active
allocator.  This matters when `MULH` appears inside another source
instruction's inline sequence. -/
def mulhBlock (v_sx v_sy v_tmp : VReg)
    (dst : Dst) (lhs rhs : Src) (tail : Program) : Program :=
  .instr (.VirtualMovsign (.vreg v_sx) lhs) <|
  .instr (.VirtualMovsign (.vreg v_sy) rhs) <|
  .instr (.MUL (.vreg v_sx) (.vreg v_sx) rhs) <|
  .instr (.MUL (.vreg v_sy) (.vreg v_sy) lhs) <|
  .instr (.MULHU (.vreg v_tmp) lhs rhs) <|
  .instr (.ADD (.vreg v_tmp) (.vreg v_tmp) (.vreg v_sx)) <|
  .instr (.ADD dst (.vreg v_tmp) (.vreg v_sy)) <|
  tail

/-- Rust's RV64 `MULH::inline_sequence`, with allocator outputs fixed as the
first three Rust scratch registers. -/
def mulhProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualMovsign (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualMovsign (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp0) (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp1) (.vreg inlineTmp1) (.xreg rs1)) <|
  .instr (.MULHU (.vreg inlineTmp2) (.xreg rs1) (.xreg rs2)) <|
  .instr (.ADD (.vreg inlineTmp2) (.vreg inlineTmp2) (.vreg inlineTmp0)) <|
  .instr (.ADD (.xreg rd) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `MULHSU::inline_sequence`, with allocator outputs fixed as the
first four Rust scratch registers. -/
def mulhsuProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualMovsign (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.ANDI (.vreg inlineTmp1) (.vreg inlineTmp0) 1) <|
  .instr (.XOR (.vreg inlineTmp2) (.xreg rs1) (.vreg inlineTmp0)) <|
  .instr (.ADD (.vreg inlineTmp2) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.MULHU (.vreg inlineTmp3) (.vreg inlineTmp2) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp2) (.vreg inlineTmp2) (.xreg rs2)) <|
  .instr (.XOR (.vreg inlineTmp3) (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .instr (.XOR (.vreg inlineTmp2) (.vreg inlineTmp2) (.vreg inlineTmp0)) <|
  .instr (.ADD (.vreg inlineTmp0) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.SLTU (.vreg inlineTmp0) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  .instr (.ADD (.xreg rd) (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .done RETIRE_SUCCESS

end JoltISA
