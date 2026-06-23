import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Mul

/-!
# DIV/REM Jolt expansion programs

Canonical bytecode expansions for the advice-verified RV64 DIV/REM family.
Proof-facing phase decompositions remain in `InstructionEquivalence`.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Jolt ISA program for RV64 `DIV`. The advice values are explicit oracle
inputs: quotient and absolute remainder. -/
def divProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAdvice inlineTmp1 remAbs) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg inlineTmp0)) <|
  .instr (.VirtualChangeDivisor (.vreg inlineTmp2) (.xreg rs1) (.xreg rs2)) <|
  mulhBlock inlineTmp4 inlineTmp5 inlineTmp6
    (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp2) <|
  .instr (.MUL (.vreg inlineTmp4) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  sraiBlock (.vreg inlineTmp5) (.vreg inlineTmp4) (63 : BitVec 6) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp5)) <|
  sraiBlock (.vreg inlineTmp3) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp5) (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.SUB (.vreg inlineTmp5) (.vreg inlineTmp5) (.vreg inlineTmp3)) <|
  .instr (.ADD (.vreg inlineTmp4) (.vreg inlineTmp4) (.vreg inlineTmp5)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp4) (.xreg rs1)) <|
  sraiBlock (.vreg inlineTmp3) (.vreg inlineTmp2) (63 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp5) (.vreg inlineTmp2) (.vreg inlineTmp3)) <|
  .instr (.SUB (.vreg inlineTmp5) (.vreg inlineTmp5) (.vreg inlineTmp3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.vreg inlineTmp5)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `DIVU`. The quotient advice is explicit. -/
def divuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp1) (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp1) (.xreg rs1)) <|
  .instr (.SUB (.vreg inlineTmp1) (.xreg rs1) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `DIVW`.

The advice values are explicit oracle inputs: the 32-bit signed quotient
loaded into `v0`, and the absolute remainder loaded into `v1`.
-/
def divwProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAdvice inlineTmp1 remAbs) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp6) (.xreg rs1)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp5) (.xreg rs2)) <|
  .instr (.VirtualAssertValidDiv0 (.vreg inlineTmp5) (.vreg inlineTmp0)) <|
  .instr (.VirtualChangeDivisorW (.vreg inlineTmp2) (.vreg inlineTmp6) (.vreg inlineTmp5)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp1) (32 : BitVec 6) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp4) (.xreg (regidx.Regidx 0))) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp6) (31 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp5) (.vreg inlineTmp1) (.vreg inlineTmp4)) <|
  .instr (.SUB (.vreg inlineTmp5) (.vreg inlineTmp5) (.vreg inlineTmp4)) <|
  .instr (.MUL (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  .instr (.ADD (.vreg inlineTmp3) (.vreg inlineTmp3) (.vreg inlineTmp5)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp6)) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp2) (31 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp3) (.vreg inlineTmp2) (.vreg inlineTmp4)) <|
  .instr (.SUB (.vreg inlineTmp3) (.vreg inlineTmp3) (.vreg inlineTmp4)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg inlineTmp0)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `DIVUW`. The quotient advice is explicit. -/
def divuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.VirtualAdvice inlineTmp2 quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.MUL (.vreg inlineTmp3) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .instr (.SUB (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp3) (.vreg inlineTmp1)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp3) (.vreg inlineTmp2)) <|
  .instr (.VirtualAssertValidDiv0 (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp3) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REM`. The advice values are explicit oracle
inputs: quotient and absolute remainder. -/
def remProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAdvice inlineTmp1 remAbs) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg inlineTmp0)) <|
  .instr (.VirtualChangeDivisor (.vreg inlineTmp2) (.xreg rs1) (.xreg rs2)) <|
  mulhBlock inlineTmp4 inlineTmp5 inlineTmp6
    (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp2) <|
  .instr (.MUL (.vreg inlineTmp4) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  sraiBlock (.vreg inlineTmp5) (.vreg inlineTmp4) (63 : BitVec 6) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp5)) <|
  sraiBlock (.vreg inlineTmp3) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp5) (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.SUB (.vreg inlineTmp5) (.vreg inlineTmp5) (.vreg inlineTmp3)) <|
  .instr (.ADD (.vreg inlineTmp4) (.vreg inlineTmp4) (.vreg inlineTmp5)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp4) (.xreg rs1)) <|
  sraiBlock (.vreg inlineTmp3) (.vreg inlineTmp2) (63 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp4) (.vreg inlineTmp2) (.vreg inlineTmp3)) <|
  .instr (.SUB (.vreg inlineTmp4) (.vreg inlineTmp4) (.vreg inlineTmp3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.vreg inlineTmp4)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp5) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REMU`. The quotient advice is explicit. -/
def remuProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.vreg inlineTmp0) (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.SUB (.vreg inlineTmp0) (.xreg rs1) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.ADDI (.xreg rd) (.vreg inlineTmp0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REMW`.

The advice values are explicit oracle inputs: the 32-bit signed quotient
loaded into `v0`, and the absolute remainder loaded into `v1`.
-/
def remwProgram (rs2 rs1 rd : regidx)
    (quotient remAbs : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualAdvice inlineTmp0 quotient) <|
  .instr (.VirtualAdvice inlineTmp1 remAbs) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp6) (.xreg rs1)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp5) (.xreg rs2)) <|
  .instr (.VirtualAssertValidDiv0 (.vreg inlineTmp5) (.vreg inlineTmp0)) <|
  .instr (.VirtualChangeDivisorW (.vreg inlineTmp2) (.vreg inlineTmp6) (.vreg inlineTmp5)) <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp0)) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp1) (32 : BitVec 6) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp4) (.xreg (regidx.Regidx 0))) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp6) (31 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp5) (.vreg inlineTmp1) (.vreg inlineTmp4)) <|
  .instr (.SUB (.vreg inlineTmp5) (.vreg inlineTmp5) (.vreg inlineTmp4)) <|
  .instr (.MUL (.vreg inlineTmp3) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  .instr (.ADD (.vreg inlineTmp3) (.vreg inlineTmp3) (.vreg inlineTmp5)) <|
  .instr (.VirtualAssertEQ (.vreg inlineTmp3) (.vreg inlineTmp6)) <|
  sraiBlock (.vreg inlineTmp4) (.vreg inlineTmp2) (31 : BitVec 6) <|
  .instr (.XOR (.vreg inlineTmp3) (.vreg inlineTmp2) (.vreg inlineTmp4)) <|
  .instr (.SUB (.vreg inlineTmp3) (.vreg inlineTmp3) (.vreg inlineTmp4)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp1) (.vreg inlineTmp3)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg inlineTmp5)) <|
  .done RETIRE_SUCCESS

/-- Jolt ISA program for RV64 `REMUW`. The quotient advice is explicit. -/
def remuwProgram (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg inlineTmp1) (.xreg rs2)) <|
  .instr (.VirtualAdvice inlineTmp2 quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.MUL (.vreg inlineTmp2) (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualAssertLTE (.vreg inlineTmp2) (.vreg inlineTmp0)) <|
  .instr (.SUB (.vreg inlineTmp2) (.vreg inlineTmp0) (.vreg inlineTmp2)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg inlineTmp2) (.vreg inlineTmp1)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg inlineTmp2)) <|
  .done RETIRE_SUCCESS

end JoltISA
