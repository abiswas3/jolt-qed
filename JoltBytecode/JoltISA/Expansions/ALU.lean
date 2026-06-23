import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Jolt ISA ALU expansions

These programs are the handwritten Jolt-ISA layer for ALU bytecode
expansions.  They are intentionally close to the Rust `inline_sequence`
methods: each constructor below corresponds to one emitted Jolt instruction,
and temporary virtual registers are written explicitly.

The fixed temporary convention used here follows Rust's allocator:
`inlineTmp0` is virtual register 40, `inlineTmp1` is virtual register 41, and
so on.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust `v_pow2` for `SLL` and `SLLW`. -/
abbrev aluPow2VReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRL` and `SRA`. -/
abbrev aluBitmaskVReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRLW`. -/
abbrev srlwBitmaskVReg : VReg := inlineTmp0

/-- Rust `v_rs1` for `SRLW`. -/
abbrev srlwRs1VReg : VReg := inlineTmp1

/-- Rust `v_rs1` for `SRAW`. -/
abbrev srawRs1VReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRAW`. -/
abbrev srawBitmaskVReg : VReg := inlineTmp1

/-- Rust `v_rs1` for `SRLIW` and `SRAIW`. -/
abbrev shiftImmediateWordRs1VReg : VReg := inlineTmp0

/-- Bitmask immediate used by RV64 `VirtualSRLI` for `SRLI`.  Its trailing-zero
count is the six-bit shift amount. -/
def srliBitmask (shamt : BitVec 6) : Nat :=
  let shift := shamt.toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Bitmask immediate used by RV64 `VirtualSRAI` for `SRAI`.  It has the same
encoding as `srliBitmask`; only the consuming virtual instruction differs. -/
def sraiBitmask (shamt : BitVec 6) : Nat :=
  srliBitmask shamt

/-- Bitmask immediate used by RV64 `VirtualSRLI` for `SRLIW`.  The source word
is first shifted left by 32, so the encoded right shift is `shamt + 32`. -/
def srliwBitmask (shamt : BitVec 5) : Nat :=
  let shift := shamt.toNat + 32
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Bitmask immediate used by RV64 `VirtualSRAI` for `SRAIW`. -/
def sraiwBitmask (shamt : BitVec 5) : Nat :=
  let shift := shamt.toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Immediate multiplier used by Rust's `SLLI` inline sequence. -/
def slliMultiplier (shamt : BitVec 6) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ shamt.toNat)

/-- Rust `SLLI::inline_sequence`: multiply by the immediate power of two. -/
def slliBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualMULI dst src (slliMultiplier shamt)) tail

/-- Rust `SLL::inline_sequence`: compute `2 ^ shift[5:0]` in a scratch
virtual register, then multiply the value by that power of two. -/
def sllBlock (dst : Dst) (value shift : Src) (scratch : VReg)
    (tail : Program) : Program :=
  .instr (.VirtualPow2 (.vreg scratch) shift) <|
  .instr (.MUL dst value (.vreg scratch)) tail

/-- Rust `SRAI::inline_sequence`: run `VirtualSRAI` with the encoded bitmask. -/
def sraiBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualSRAI dst src (sraiBitmask shamt)) tail

/-- Rust `SRLI::inline_sequence`: run `VirtualSRLI` with the encoded bitmask. -/
def srliBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualSRLI dst src (srliBitmask shamt)) tail

/-- Rust `SRL::inline_sequence`: compute the right-shift bitmask in a scratch
virtual register, then run `VirtualSRL` with that bitmask. -/
def srlBlock (dst : Dst) (value shift : Src) (scratch : VReg)
    (tail : Program) : Program :=
  .instr (.VirtualShiftRightBitmask (.vreg scratch) shift) <|
  .instr (.VirtualSRL dst value (.vreg scratch)) tail

/-- `SLL`: compute `2 ^ rs2[5:0]` in Rust's first scratch register, then
multiply `rs1` by it. -/
def sllProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualPow2 (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.xreg rd) (.xreg rs1) (.vreg inlineTmp0)) <|
  .done RETIRE_SUCCESS

/-- `SLLI`: multiply `rs1` by the immediate power of two. -/
def slliProgram (shamt : BitVec 6) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  slliBlock (.xreg rd) (.xreg rs1) shamt <|
  .done RETIRE_SUCCESS

/-- `SRL`: compute a right-shift bitmask in Rust's first scratch register,
then run `VirtualSRL`. -/
def srlProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualSRL (.xreg rd) (.xreg rs1) (.vreg inlineTmp0)) <|
  .done RETIRE_SUCCESS

/-- `SRLI`: run `VirtualSRLI` with the statically encoded bitmask. -/
def srliProgram (shamt : BitVec 6) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSRLI (.xreg rd) (.xreg rs1) (srliBitmask shamt)) <|
  .done RETIRE_SUCCESS

/-- `SRA`: compute a right-shift bitmask in Rust's first scratch register,
then run `VirtualSRA`. -/
def sraProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.VirtualSRA (.xreg rd) (.xreg rs1) (.vreg inlineTmp0)) <|
  .done RETIRE_SUCCESS

/-- `SRAI`: run `VirtualSRAI` with the statically encoded bitmask. -/
def sraiProgram (shamt : BitVec 6) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSRAI (.xreg rd) (.xreg rs1) (sraiBitmask shamt)) <|
  .done RETIRE_SUCCESS

/-- `ADDW` as reached through Rust `Instruction::trace`.

If the destination is architectural register `x0`, Rust emits the pure
writeback no-op replacement `ADDI x0, x0, 0`; otherwise it uses ADDW's
ordinary instruction-specific `inline_sequence`. -/
def addwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SUBW`: ordinary 64-bit `SUB`, then virtual sign-extend-word. -/
def subwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `MULW`: ordinary 64-bit `MUL`, then virtual sign-extend-word. -/
def mulwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SLLW`: compute `2 ^ rs2[4:0]` in Rust's first scratch register,
multiply, then sign-extend. -/
def sllwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualPow2W (.vreg inlineTmp0) (.xreg rs2)) <|
  .instr (.MUL (.xreg rd) (.xreg rs1) (.vreg inlineTmp0)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRLW`: shift `rs1` left into the high word, encode `rs2 | 32` as a
bitmask, logically shift right, then sign-extend. -/
def srlwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  slliBlock (.vreg inlineTmp1) (.xreg rs1) (32 : BitVec 6) <|
  .instr (.ORI (.vreg inlineTmp0) (.xreg rs2) (32 : BitVec 12)) <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp0) (.vreg inlineTmp0)) <|
  .instr (.VirtualSRL (.xreg rd) (.vreg inlineTmp1) (.vreg inlineTmp0)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRAW`: sign-extend the low word into Rust's first scratch register, mask
the shift amount in Rust's second scratch register, encode that mask in place as a
bitmask, arithmetically shift right, then sign-extend. -/
def srawProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.ANDI (.vreg inlineTmp1) (.xreg rs2) (0x1f : BitVec 12)) <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp1) (.vreg inlineTmp1)) <|
  .instr (.VirtualSRA (.xreg rd) (.vreg inlineTmp0) (.vreg inlineTmp1)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `ADDIW`: ordinary `ADDI`, then virtual sign-extend-word. -/
def addiwProgram (imm : BitVec 12) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.ADDI (.xreg rd) (.xreg rs1) imm) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SLLIW`: multiply by the immediate power of two, then sign-extend. -/
def slliwProgram (shamt : BitVec 5) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualMULI (.xreg rd) (.xreg rs1) (BitVec.ofNat 64 (2 ^ shamt.toNat))) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRLIW`: shift `rs1` left into the high word, logically shift right by the
encoded immediate bitmask, then sign-extend. -/
def srliwProgram (shamt : BitVec 5) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  slliBlock (.vreg inlineTmp0) (.xreg rs1) (32 : BitVec 6) <|
  .instr (.VirtualSRLI (.xreg rd) (.vreg inlineTmp0) (srliwBitmask shamt)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRAIW`: sign-extend `rs1[31:0]` into Rust's first scratch register,
arithmetically shift right by the encoded immediate bitmask, then sign-extend
again. -/
def sraiwProgram (shamt : BitVec 5) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSignExtendWord (.vreg inlineTmp0) (.xreg rs1)) <|
  .instr (.VirtualSRAI (.xreg rd) (.vreg inlineTmp0) (sraiwBitmask shamt)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

end JoltISA
