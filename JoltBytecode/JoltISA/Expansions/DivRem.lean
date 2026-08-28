import JoltBytecode.JoltISA.Expansions.ALU

/-!
# Jolt ISA unsigned DIV/REM expansion programs

The signed `DIV`, `DIVW`, `REM`, and `REMW` handwritten programs were removed
because current Rust uses different one-advice expansions. Their generated
programs in `ExpansionsAutomated.lean` are now the source of truth.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Jolt ISA program for RV64 `DIVU`. The quotient advice is explicit. -/
def divuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice (.vreg inlineTmp0) quotient) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp1) (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp1) (.xreg rs1)) <|
  .instr (.SUB (.vreg inlineTmp1) (.xreg rs1) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `DIVUW`. The quotient advice is explicit. -/
def divuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.VirtualAdvice (.vreg inlineTmp2) quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.MUL (.vreg inlineTmp3) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .instr (.SUB (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp3) (.vreg inlineTmp1)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp3) (.vreg inlineTmp2)) <|
  .instr (.VirtualAssertValidDiv0 (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp3) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REMU`. The quotient advice is explicit. -/
def remuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice (.vreg inlineTmp0) quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp0) (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.SUB (.vreg inlineTmp0) (.xreg rs1) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REMUW`. The quotient advice is explicit. -/
def remuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.VirtualAdvice (.vreg inlineTmp2) quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.MUL (.vreg inlineTmp2) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp2) (.vreg inlineTmp0)) <|
  .instr (.SUB (.vreg inlineTmp2) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg inlineTmp2)) <|
  .done RETIRE_SUCCESS

end JoltISA
