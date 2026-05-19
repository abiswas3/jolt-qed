import JoltBytecode.JoltISA.Instruction

/-!
# Jolt ISA ALU expansions

These programs are the handwritten Jolt-ISA layer for ALU bytecode
expansions.  They are intentionally close to the Rust `inline_sequence`
methods: each constructor below corresponds to one emitted Jolt instruction,
and temporary virtual registers are written explicitly.

The fixed temporary convention used here matches the existing hand proofs:
`v0` is the first scratch register and `v1` is the second scratch register.
Later Rust-to-Lean extraction should replace these handwritten programs, but
the theorem statements should not need to change.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

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

/-- Rust `SRAI::inline_sequence`: run `VirtualSRAI` with the encoded bitmask. -/
def sraiBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualSRAI dst src (sraiBitmask shamt)) tail

/-- `SLL`: compute `2 ^ rs2[5:0]` in `v0`, then multiply `rs1` by it. -/
def sllProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualPow2 (.vreg 0) (.xreg rs2)) <|
  .instr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0)) <|
  .done RETIRE_SUCCESS

/-- `SLLI`: multiply `rs1` by the immediate power of two. -/
def slliProgram (shamt : BitVec 6) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  slliBlock (.xreg rd) (.xreg rs1) shamt <|
  .done RETIRE_SUCCESS

/-- `SRL`: compute a right-shift bitmask in `v0`, then run `VirtualSRL`. -/
def srlProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualShiftRightBitmask (.vreg 0) (.xreg rs2)) <|
  .instr (.VirtualSRL (.xreg rd) (.xreg rs1) (.vreg 0)) <|
  .done RETIRE_SUCCESS

/-- `SRLI`: run `VirtualSRLI` with the statically encoded bitmask. -/
def srliProgram (shamt : BitVec 6) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSRLI (.xreg rd) (.xreg rs1) (srliBitmask shamt)) <|
  .done RETIRE_SUCCESS

/-- `SRA`: compute a right-shift bitmask in `v0`, then run `VirtualSRA`. -/
def sraProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualShiftRightBitmask (.vreg 0) (.xreg rs2)) <|
  .instr (.VirtualSRA (.xreg rd) (.xreg rs1) (.vreg 0)) <|
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

/-- `SLLW`: compute `2 ^ rs2[4:0]` in `v0`, multiply, then sign-extend. -/
def sllwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualPow2W (.vreg 0) (.xreg rs2)) <|
  .instr (.MUL (.xreg rd) (.xreg rs1) (.vreg 0)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRLW`: shift `rs1` left into the high word, encode `rs2 | 32` as a
bitmask, logically shift right, then sign-extend. -/
def srlwProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  slliBlock (.vreg 0) (.xreg rs1) (32 : BitVec 6) <|
  .instr (.ORI (.vreg 1) (.xreg rs2) (32 : BitVec 12)) <|
  .instr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1)) <|
  .instr (.VirtualSRL (.xreg rd) (.vreg 0) (.vreg 1)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRAW`: sign-extend the low word into `v0`, mask the shift amount in `v1`,
encode that mask as a bitmask, arithmetically shift right, then sign-extend. -/
def srawProgram (rs2 rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSignExtendWord (.vreg 0) (.xreg rs1)) <|
  .instr (.ANDI (.vreg 1) (.xreg rs2) (0x1f : BitVec 12)) <|
  .instr (.VirtualShiftRightBitmask (.vreg 1) (.vreg 1)) <|
  .instr (.VirtualSRA (.xreg rd) (.vreg 0) (.vreg 1)) <|
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
  slliBlock (.vreg 0) (.xreg rs1) (32 : BitVec 6) <|
  .instr (.VirtualSRLI (.xreg rd) (.vreg 0) (srliwBitmask shamt)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

/-- `SRAIW`: sign-extend `rs1[31:0]` into `v1`, arithmetically shift right by
the encoded immediate bitmask, then sign-extend again. -/
def sraiwProgram (shamt : BitVec 5) (rs1 rd : regidx) : Program :=
  pureWritebackTraceProgram rd <|
  .instr (.VirtualSignExtendWord (.vreg 1) (.xreg rs1)) <|
  .instr (.VirtualSRAI (.xreg rd) (.vreg 1) (sraiwBitmask shamt)) <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.xreg rd)) <|
  .done RETIRE_SUCCESS

end JoltISA
