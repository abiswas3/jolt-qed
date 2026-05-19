import JoltBytecode.JoltISA.Semantics

/-!
# M-extension Jolt expansion programs

These definitions are data, not proofs.  They are intentionally close to the
Rust inline sequences and are the shape a future Rust-to-Lean extractor should
produce.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's RV64 `MULH::inline_sequence`, with allocator outputs fixed as
`v_sx = 0`, `v_sy = 1`, `v_tmp = 2`. -/
def mulhProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualMovsign (.vreg 0) (.xreg rs1)) <|
  .instr (.VirtualMovsign (.vreg 1) (.xreg rs2)) <|
  .instr (.MUL (.vreg 0) (.vreg 0) (.xreg rs2)) <|
  .instr (.MUL (.vreg 1) (.vreg 1) (.xreg rs1)) <|
  .instr (.MULHU (.vreg 2) (.xreg rs1) (.xreg rs2)) <|
  .instr (.ADD (.vreg 2) (.vreg 2) (.vreg 0)) <|
  .instr (.ADD (.xreg rd) (.vreg 2) (.vreg 1)) <|
  .done RETIRE_SUCCESS

/-- Rust's RV64 `MULHSU::inline_sequence`, with allocator outputs fixed as
`v0 = 0`, `v1 = 1`, `v2 = 2`, `v3 = 3`. -/
def mulhsuProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualMovsign (.vreg 0) (.xreg rs1)) <|
  .instr (.ANDI (.vreg 1) (.vreg 0) 1) <|
  .instr (.XOR (.vreg 2) (.xreg rs1) (.vreg 0)) <|
  .instr (.ADD (.vreg 2) (.vreg 2) (.vreg 1)) <|
  .instr (.MULHU (.vreg 3) (.vreg 2) (.xreg rs2)) <|
  .instr (.MUL (.vreg 2) (.vreg 2) (.xreg rs2)) <|
  .instr (.XOR (.vreg 3) (.vreg 3) (.vreg 0)) <|
  .instr (.XOR (.vreg 2) (.vreg 2) (.vreg 0)) <|
  .instr (.ADD (.vreg 0) (.vreg 2) (.vreg 1)) <|
  .instr (.SLTU (.vreg 0) (.vreg 0) (.vreg 2)) <|
  .instr (.ADD (.xreg rd) (.vreg 3) (.vreg 0)) <|
  .done RETIRE_SUCCESS

end JoltISA
