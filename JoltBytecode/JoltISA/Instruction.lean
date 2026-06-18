import JoltBytecode.JoltISA.Values

/-!
# Jolt ISA syntax

This is the data layer for final Jolt trace-row instructions.  Source
instructions that Rust lowers through `inline_sequence` belong in the expansion
layer, not as constructors here.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

inductive Instr where
  | NoOp
  | ADDI (dst : Dst) (src : Src) (imm : BitVec 12)
  | ANDI (dst : Dst) (src : Src) (imm : BitVec 12)
  | ORI  (dst : Dst) (src : Src) (imm : BitVec 12)
  | XORI (dst : Dst) (src : Src) (imm : BitVec 12)
  | SLTI (dst : Dst) (src : Src) (imm : BitVec 12)
  | SLTIU (dst : Dst) (src : Src) (imm : BitVec 12)
  | LUI  (dst : Dst) (imm : BitVec 64)
  | AUIPC (dst : Dst) (imm : BitVec 20)
  | JAL (dst : Dst) (imm : BitVec 21)
  | JALR (dst : Dst) (base : Src) (imm : BitVec 12)
  | BEQ (lhs rhs : Src) (imm : BitVec 13)
  | BNE (lhs rhs : Src) (imm : BitVec 13)
  | BLT (lhs rhs : Src) (imm : BitVec 13)
  | BGE (lhs rhs : Src) (imm : BitVec 13)
  | BLTU (lhs rhs : Src) (imm : BitVec 13)
  | BGEU (lhs rhs : Src) (imm : BitVec 13)
  | FENCE
  | ADD  (dst : Dst) (lhs rhs : Src)
  | SUB  (dst : Dst) (lhs rhs : Src)
  | MUL  (dst : Dst) (lhs rhs : Src)
  | MULHU (dst : Dst) (lhs rhs : Src)
  | ANDN (dst : Dst) (lhs rhs : Src)
  | VirtualMULI (dst : Dst) (src : Src) (imm : BitVec 64)
  | VirtualPow2 (dst : Dst) (src : Src)
  | VirtualPow2W (dst : Dst) (src : Src)
  | VirtualPow2I (dst : Dst) (imm : Nat)
  | VirtualPow2IW (dst : Dst) (imm : Nat)
  | VirtualShiftRightBitmask (dst : Dst) (src : Src)
  | VirtualShiftRightBitmaskI (dst : Dst) (imm : Nat)
  | VirtualSRLI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRAI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRL (dst : Dst) (value bitmask : Src)
  | VirtualSRA (dst : Dst) (value bitmask : Src)
  | VirtualROTRI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualROTRIW (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualRev8W (dst : Dst) (src : Src)
  | VirtualXORROT32 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT24 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT16 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT63 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW16 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW12 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW8 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW7 (dst : Dst) (lhs rhs : Src)
  | OR   (dst : Dst) (lhs rhs : Src)
  | XOR  (dst : Dst) (lhs rhs : Src)
  | AND  (dst : Dst) (lhs rhs : Src)
  | SLT  (dst : Dst) (lhs rhs : Src)
  | SLTU (dst : Dst) (lhs rhs : Src)
  | VirtualSignExtendWord (dst : Dst) (src : Src)
  | VirtualZeroExtendWord (dst : Dst) (src : Src)
  | VirtualMovsign (dst : Dst) (src : Src)
  | VirtualAssertHalfwordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
  | VirtualAssertWordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
  | LD (dst : Dst) (base : Src) (imm : BitVec 12)
  | SD (base value : Src) (imm : BitVec 12)
  | VirtualAdvice (vd : VReg) (value : BitVec 64)
  | VirtualAdviceLoad (dst : Dst) (value : BitVec 64)
  | VirtualAdviceLen (dst : Dst) (remaining : BitVec 64)
  | VirtualHostIO
  | VirtualAssertEQ (lhs rhs : Src)
  | VirtualAssertValidDiv0 (divisor quotient : Src)
  | VirtualChangeDivisor (dst : Dst) (dividend divisor : Src)
  | VirtualChangeDivisorW (dst : Dst) (dividend divisor : Src)
  | VirtualAssertValidUnsignedRemainder (remainder divisor : Src)
  | VirtualAssertMulUNoOverflow (lhs rhs : Src)
  | VirtualAssertLTE (lhs rhs : Src)
  deriving Repr


/-- Source instructions that Rust expands before final Jolt bytecode.

This mirrors the built-in `SourceInstructionKind` cases handled by
`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/mod.rs`
in `expand_source_only_instruction`. -/
inductive Expanded where
  | ADDIW (dst : Dst) (src : Src) (imm : BitVec 12)
  | ADDW (dst : Dst) (lhs rhs : Src)
  | SUBW (dst : Dst) (lhs rhs : Src)
  | MULH (dst : Dst) (lhs rhs : Src)
  | MULHSU (dst : Dst) (lhs rhs : Src)
  | MULW (dst : Dst) (lhs rhs : Src)
  | LB (dst : Dst) (base : Src) (imm : BitVec 12)
  | LBU (dst : Dst) (base : Src) (imm : BitVec 12)
  | LH (dst : Dst) (base : Src) (imm : BitVec 12)
  | LHU (dst : Dst) (base : Src) (imm : BitVec 12)
  | LW (dst : Dst) (base : Src) (imm : BitVec 12)
  | LWU (dst : Dst) (base : Src) (imm : BitVec 12)
  | AdviceLB (dst : Dst) (advice : BitVec 8)
  | AdviceLH (dst : Dst) (advice : BitVec 16)
  | AdviceLW (dst : Dst) (advice : BitVec 32)
  | AdviceLD (dst : Dst) (advice : BitVec 64)
  | AMOADDD (dst : Dst) (addr value : Src)
  | AMOANDD (dst : Dst) (addr value : Src)
  | AMOORD (dst : Dst) (addr value : Src)
  | AMOXORD (dst : Dst) (addr value : Src)
  | AMOSWAPD (dst : Dst) (addr value : Src)
  | AMOMAXD (dst : Dst) (addr value : Src)
  | AMOMAXUD (dst : Dst) (addr value : Src)
  | AMOMIND (dst : Dst) (addr value : Src)
  | AMOMINUD (dst : Dst) (addr value : Src)
  | AMOADDW (dst : Dst) (addr value : Src)
  | AMOANDW (dst : Dst) (addr value : Src)
  | AMOORW (dst : Dst) (addr value : Src)
  | AMOXORW (dst : Dst) (addr value : Src)
  | AMOSWAPW (dst : Dst) (addr value : Src)
  | AMOMAXW (dst : Dst) (addr value : Src)
  | AMOMAXUW (dst : Dst) (addr value : Src)
  | AMOMINW (dst : Dst) (addr value : Src)
  | AMOMINUW (dst : Dst) (addr value : Src)
  | LRD (dst : Dst) (addr : Src)
  | LRW (dst : Dst) (addr : Src)
  | DIV (dst : Dst) (lhs rhs : Src)
  | DIVU (dst : Dst) (lhs rhs : Src)
  | DIVW (dst : Dst) (lhs rhs : Src)
  | DIVUW (dst : Dst) (lhs rhs : Src)
  | REM (dst : Dst) (lhs rhs : Src)
  | REMU (dst : Dst) (lhs rhs : Src)
  | REMW (dst : Dst) (lhs rhs : Src)
  | REMUW (dst : Dst) (lhs rhs : Src)
  | SB (base value : Src) (imm : BitVec 12)
  | SCD (dst : Dst) (addr value : Src)
  | SCW (dst : Dst) (addr value : Src)
  | SH (base value : Src) (imm : BitVec 12)
  | SW (base value : Src) (imm : BitVec 12)
  | CSRRW (dst : Dst) (src : Src) (csr : BitVec 12)
  | CSRRS (dst : Dst) (src : Src) (csr : BitVec 12)
  | EBREAK
  | ECALL
  | MRET
  | SLL (dst : Dst) (value shamt : Src)
  | SLLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SLLW (dst : Dst) (value shamt : Src)
  | SLLIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRL (dst : Dst) (value shamt : Src)
  | SRLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRA (dst : Dst) (value shamt : Src)
  | SRAI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRLIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRAIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRLW (dst : Dst) (value shamt : Src)
  | SRAW (dst : Dst) (value shamt : Src)
  deriving Repr


private def x0 : regidx := regidx.Regidx 0
private def dst : Dst := .xreg x0
private def src : Src := .xreg x0
private def vreg : VReg := 32

/-- Structured Jolt bytecode programs.

`instr i next` means: execute `i`; if it retires successfully, continue with
`next`; otherwise return the non-retire result immediately.  This is the
control-flow rule used by the Rust inline expansions for memory operations:
alignment assertions and loads can return exceptions, and the tail of the
program must not run after such a result. -/
inductive Program where
  | done (result : ExecutionResult)
  | instr (instr : Instr) (next : Program)
  deriving Repr

/-- Build the common straight-line "run every instruction, then retire"
program.  This is useful for expansions with no explicit early-return
instruction apart from the generic non-retire short-circuiting handled by
`Program.instr`. -/
def Program.seq (instrs : List Instr) : Program :=
  instrs.foldr Program.instr (.done RETIRE_SUCCESS)

/-- Append two Jolt programs.

If the first program retires successfully, execution continues with the second
program. If the first program ends with any other `ExecutionResult`, the second
program is unreachable, matching `execProgram`'s short-circuiting behavior. -/
def Program.append : Program → Program → Program
  | .done (.Retire_Success ()), second => second
  | .done result, _ => .done result
  | .instr instruction rest, second => .instr instruction (rest.append second)

/-- Rust's trace-dispatch replacement for pure writeback instructions whose
destination is architectural `x0`: emit a single no-op `ADDI x0, x0, 0` row. -/
def pureWritebackRdZeroProgram : Program :=
  .instr (.ADDI (.xreg (regidx.Regidx 0)) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Boolean test for architectural register `x0`.

The generated `regidx` type does not derive `DecidableEq`, so trace-dispatch
programs use this Boolean predicate instead of comparing registers directly. -/
def isX0 (rd : regidx) : Bool :=
  match rd with
  | regidx.Regidx bits => decide (bits.toNat = 0)

/-- Rust's trace-dispatch rule for pure writeback instructions.

If `rd = x0`, Rust emits `pureWritebackRdZeroProgram`; otherwise it uses the
instruction's ordinary inline sequence unchanged. -/
def pureWritebackTraceProgram (rd : regidx) (normal : Program) : Program :=
  if isX0 rd then pureWritebackRdZeroProgram else normal

/-- The `isX0` predicate recognizes architectural register `x0`. -/
theorem isX0_regidx_zero :
    isX0 (regidx.Regidx 0) = true := by
  unfold isX0
  simp

/-- If a register is not architectural `x0`, `isX0` returns `false`. -/
theorem isX0_eq_false_of_ne_zero
    {rd : regidx}
    (hrd : rd ≠ regidx.Regidx 0) :
    isX0 rd = false := by
  cases rd with
  | Regidx bits =>
      unfold isX0
      simp only
      apply decide_eq_false
      intro hbits
      apply hrd
      congr
      apply BitVec.eq_of_toNat_eq
      simpa using hbits

/-- For `rd = x0`, pure-writeback trace dispatch uses the no-op replacement
program. -/
theorem pureWritebackTraceProgram_regidx_zero (normal : Program) :
    pureWritebackTraceProgram (regidx.Regidx 0) normal =
      pureWritebackRdZeroProgram := by
  unfold pureWritebackTraceProgram
  rw [isX0_regidx_zero]
  simp only [↓reduceIte]

/-- For `rd ≠ x0`, pure-writeback trace dispatch uses the ordinary inline
sequence unchanged. -/
theorem pureWritebackTraceProgram_of_ne_zero
    {rd : regidx}
    (hrd : rd ≠ regidx.Regidx 0)
    (normal : Program) :
    pureWritebackTraceProgram rd normal = normal := by
  unfold pureWritebackTraceProgram
  rw [isX0_eq_false_of_ne_zero hrd]
  simp only [Bool.false_eq_true, ↓reduceIte]
