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

/-- No-operand final Jolt instruction kind.

This mirrors Rust's `JoltInstructionKind = JoltInstruction<()>` in
`crates/jolt-riscv/src/kind.rs`; source-only instructions that Rust expands
must not appear here. -/
inductive InstrKind where
  | Noop
  | Add
  | Addi
  | Sub
  | Lui
  | Auipc
  | Mul
  | MulHU
  | And
  | AndI
  | Or
  | OrI
  | Xor
  | XorI
  | Andn
  | Slt
  | SltI
  | SltU
  | SltIU
  | Beq
  | Bne
  | Blt
  | Bge
  | BltU
  | BgeU
  | Ld
  | Sd
  | Fence
  | Jal
  | Jalr
  | AssertEq
  | AssertLte
  | AssertValidDiv0
  | AssertValidUnsignedRemainder
  | AssertMulUNoOverflow
  | AssertWordAlignment
  | AssertHalfwordAlignment
  | Pow2
  | Pow2I
  | Pow2W
  | Pow2IW
  | MulI
  | MovSign
  | VirtualRev8W
  | VirtualChangeDivisor
  | VirtualChangeDivisorW
  | VirtualSignExtendWord
  | VirtualZeroExtendWord
  | VirtualSrl
  | VirtualSrli
  | VirtualSra
  | VirtualSrai
  | VirtualShiftRightBitmask
  | VirtualShiftRightBitmaski
  | VirtualRotri
  | VirtualRotriw
  | VirtualXorRot32
  | VirtualXorRot24
  | VirtualXorRot16
  | VirtualXorRot63
  | VirtualXorRotW16
  | VirtualXorRotW12
  | VirtualXorRotW8
  | VirtualXorRotW7
  | VirtualAdvice
  | VirtualAdviceLen
  | VirtualAdviceLoad
  | VirtualHostIO
  deriving Repr, DecidableEq

namespace InstrKind

/-- Rust final enum order from
`crates/jolt-riscv/src/instructions/mod.rs::JoltInstruction`.

`Noop` is included here because it is in `JoltInstruction`; Rust's
`for_each_jolt_instruction_kind!` macro handles `Noop` separately. -/
def rustOrder : List InstrKind :=
  [.Noop, .Add, .Addi, .Sub, .Lui, .Auipc, .Mul, .MulHU, .And, .AndI, .Or, .OrI,
    .Xor, .XorI, .Andn, .Slt, .SltI, .SltU, .SltIU, .Beq, .Bne, .Blt, .Bge,
    .BltU, .BgeU, .Ld, .Sd, .Fence, .Jal, .Jalr, .AssertEq, .AssertLte,
    .AssertValidDiv0, .AssertValidUnsignedRemainder, .AssertMulUNoOverflow,
    .AssertWordAlignment, .AssertHalfwordAlignment, .Pow2, .Pow2I, .Pow2W,
    .Pow2IW, .MulI, .MovSign, .VirtualRev8W, .VirtualChangeDivisor,
    .VirtualChangeDivisorW, .VirtualSignExtendWord, .VirtualZeroExtendWord,
    .VirtualSrl, .VirtualSrli, .VirtualSra, .VirtualSrai,
    .VirtualShiftRightBitmask, .VirtualShiftRightBitmaski, .VirtualRotri,
    .VirtualRotriw, .VirtualXorRot32, .VirtualXorRot24, .VirtualXorRot16,
    .VirtualXorRot63, .VirtualXorRotW16, .VirtualXorRotW12, .VirtualXorRotW8,
    .VirtualXorRotW7, .VirtualAdvice, .VirtualAdviceLen, .VirtualAdviceLoad,
    .VirtualHostIO]

theorem mem_rustOrder (kind : InstrKind) : kind ∈ rustOrder := by
  cases kind <;> decide

end InstrKind

namespace Instr

/-- Forget operands and recover the final Rust instruction kind. -/
def kind : Instr → InstrKind
  | .NoOp => .Noop
  | .ADDI _ _ _ => .Addi
  | .ANDI _ _ _ => .AndI
  | .ORI _ _ _ => .OrI
  | .XORI _ _ _ => .XorI
  | .SLTI _ _ _ => .SltI
  | .SLTIU _ _ _ => .SltIU
  | .LUI _ _ => .Lui
  | .AUIPC _ _ => .Auipc
  | .JAL _ _ => .Jal
  | .JALR _ _ _ => .Jalr
  | .BEQ _ _ _ => .Beq
  | .BNE _ _ _ => .Bne
  | .BLT _ _ _ => .Blt
  | .BGE _ _ _ => .Bge
  | .BLTU _ _ _ => .BltU
  | .BGEU _ _ _ => .BgeU
  | .FENCE => .Fence
  | .ADD _ _ _ => .Add
  | .SUB _ _ _ => .Sub
  | .MUL _ _ _ => .Mul
  | .MULHU _ _ _ => .MulHU
  | .ANDN _ _ _ => .Andn
  | .VirtualMULI _ _ _ => .MulI
  | .VirtualPow2 _ _ => .Pow2
  | .VirtualPow2W _ _ => .Pow2W
  | .VirtualPow2I _ _ => .Pow2I
  | .VirtualPow2IW _ _ => .Pow2IW
  | .VirtualShiftRightBitmask _ _ => .VirtualShiftRightBitmask
  | .VirtualShiftRightBitmaskI _ _ => .VirtualShiftRightBitmaski
  | .VirtualSRLI _ _ _ => .VirtualSrli
  | .VirtualSRAI _ _ _ => .VirtualSrai
  | .VirtualSRL _ _ _ => .VirtualSrl
  | .VirtualSRA _ _ _ => .VirtualSra
  | .VirtualROTRI _ _ _ => .VirtualRotri
  | .VirtualROTRIW _ _ _ => .VirtualRotriw
  | .VirtualRev8W _ _ => .VirtualRev8W
  | .VirtualXORROT32 _ _ _ => .VirtualXorRot32
  | .VirtualXORROT24 _ _ _ => .VirtualXorRot24
  | .VirtualXORROT16 _ _ _ => .VirtualXorRot16
  | .VirtualXORROT63 _ _ _ => .VirtualXorRot63
  | .VirtualXORROTW16 _ _ _ => .VirtualXorRotW16
  | .VirtualXORROTW12 _ _ _ => .VirtualXorRotW12
  | .VirtualXORROTW8 _ _ _ => .VirtualXorRotW8
  | .VirtualXORROTW7 _ _ _ => .VirtualXorRotW7
  | .OR _ _ _ => .Or
  | .XOR _ _ _ => .Xor
  | .AND _ _ _ => .And
  | .SLT _ _ _ => .Slt
  | .SLTU _ _ _ => .SltU
  | .VirtualSignExtendWord _ _ => .VirtualSignExtendWord
  | .VirtualZeroExtendWord _ _ => .VirtualZeroExtendWord
  | .VirtualMovsign _ _ => .MovSign
  | .VirtualAssertHalfwordAlignment _ _ _ => .AssertHalfwordAlignment
  | .VirtualAssertWordAlignment _ _ _ => .AssertWordAlignment
  | .LD _ _ _ => .Ld
  | .SD _ _ _ => .Sd
  | .VirtualAdvice _ _ => .VirtualAdvice
  | .VirtualAdviceLoad _ _ => .VirtualAdviceLoad
  | .VirtualAdviceLen _ _ => .VirtualAdviceLen
  | .VirtualHostIO => .VirtualHostIO
  | .VirtualAssertEQ _ _ => .AssertEq
  | .VirtualAssertValidDiv0 _ _ => .AssertValidDiv0
  | .VirtualChangeDivisor _ _ _ => .VirtualChangeDivisor
  | .VirtualChangeDivisorW _ _ _ => .VirtualChangeDivisorW
  | .VirtualAssertValidUnsignedRemainder _ _ => .AssertValidUnsignedRemainder
  | .VirtualAssertMulUNoOverflow _ _ => .AssertMulUNoOverflow
  | .VirtualAssertLTE _ _ => .AssertLte

theorem kind_mem_rustOrder (instr : Instr) : instr.kind ∈ InstrKind.rustOrder :=
  InstrKind.mem_rustOrder instr.kind

end Instr

namespace InstrKind

private def x0 : regidx := regidx.Regidx 0
private def dst : Dst := .xreg x0
private def src : Src := .xreg x0
private def vreg : VReg := 32

/-- A dummy operand witness for each final kind. This fails to define if the
Lean final instruction syntax is missing a Rust kind. -/
def witness : InstrKind → Instr
  | .Noop => .NoOp
  | .Add => .ADD dst src src
  | .Addi => .ADDI dst src 0
  | .Sub => .SUB dst src src
  | .Lui => .LUI dst 0
  | .Auipc => .AUIPC dst 0
  | .Mul => .MUL dst src src
  | .MulHU => .MULHU dst src src
  | .And => .AND dst src src
  | .AndI => .ANDI dst src 0
  | .Or => .OR dst src src
  | .OrI => .ORI dst src 0
  | .Xor => .XOR dst src src
  | .XorI => .XORI dst src 0
  | .Andn => .ANDN dst src src
  | .Slt => .SLT dst src src
  | .SltI => .SLTI dst src 0
  | .SltU => .SLTU dst src src
  | .SltIU => .SLTIU dst src 0
  | .Beq => .BEQ src src 0
  | .Bne => .BNE src src 0
  | .Blt => .BLT src src 0
  | .Bge => .BGE src src 0
  | .BltU => .BLTU src src 0
  | .BgeU => .BGEU src src 0
  | .Ld => .LD dst src 0
  | .Sd => .SD src src 0
  | .Fence => .FENCE
  | .Jal => .JAL dst 0
  | .Jalr => .JALR dst src 0
  | .AssertEq => .VirtualAssertEQ src src
  | .AssertLte => .VirtualAssertLTE src src
  | .AssertValidDiv0 => .VirtualAssertValidDiv0 src src
  | .AssertValidUnsignedRemainder => .VirtualAssertValidUnsignedRemainder src src
  | .AssertMulUNoOverflow => .VirtualAssertMulUNoOverflow src src
  | .AssertWordAlignment =>
      .VirtualAssertWordAlignment x0 0 (ExceptionType.E_Load_Addr_Align ())
  | .AssertHalfwordAlignment =>
      .VirtualAssertHalfwordAlignment x0 0 (ExceptionType.E_Load_Addr_Align ())
  | .Pow2 => .VirtualPow2 dst src
  | .Pow2I => .VirtualPow2I dst 0
  | .Pow2W => .VirtualPow2W dst src
  | .Pow2IW => .VirtualPow2IW dst 0
  | .MulI => .VirtualMULI dst src 0
  | .MovSign => .VirtualMovsign dst src
  | .VirtualRev8W => .VirtualRev8W dst src
  | .VirtualChangeDivisor => .VirtualChangeDivisor dst src src
  | .VirtualChangeDivisorW => .VirtualChangeDivisorW dst src src
  | .VirtualSignExtendWord => .VirtualSignExtendWord dst src
  | .VirtualZeroExtendWord => .VirtualZeroExtendWord dst src
  | .VirtualSrl => .VirtualSRL dst src src
  | .VirtualSrli => .VirtualSRLI dst src 0
  | .VirtualSra => .VirtualSRA dst src src
  | .VirtualSrai => .VirtualSRAI dst src 0
  | .VirtualShiftRightBitmask => .VirtualShiftRightBitmask dst src
  | .VirtualShiftRightBitmaski => .VirtualShiftRightBitmaskI dst 0
  | .VirtualRotri => .VirtualROTRI dst src 0
  | .VirtualRotriw => .VirtualROTRIW dst src 0
  | .VirtualXorRot32 => .VirtualXORROT32 dst src src
  | .VirtualXorRot24 => .VirtualXORROT24 dst src src
  | .VirtualXorRot16 => .VirtualXORROT16 dst src src
  | .VirtualXorRot63 => .VirtualXORROT63 dst src src
  | .VirtualXorRotW16 => .VirtualXORROTW16 dst src src
  | .VirtualXorRotW12 => .VirtualXORROTW12 dst src src
  | .VirtualXorRotW8 => .VirtualXORROTW8 dst src src
  | .VirtualXorRotW7 => .VirtualXORROTW7 dst src src
  | .VirtualAdvice => .VirtualAdvice vreg 0
  | .VirtualAdviceLen => .VirtualAdviceLen dst 0
  | .VirtualAdviceLoad => .VirtualAdviceLoad dst 0
  | .VirtualHostIO => .VirtualHostIO

theorem witness_kind (kind : InstrKind) : kind.witness.kind = kind := by
  cases kind <;> rfl

end InstrKind

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

end JoltISA
