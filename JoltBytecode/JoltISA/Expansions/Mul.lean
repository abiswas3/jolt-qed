import JoltBytecode.JoltISA.Semantics

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
