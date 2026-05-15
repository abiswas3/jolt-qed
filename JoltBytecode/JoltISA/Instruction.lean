import JoltBytecode.JoltISA.Values

/-!
# Jolt ISA syntax

This is the data layer that Rust extraction should eventually target.  The
constructors intentionally stay close to the inline bytecode instructions
rather than baking in proof-specific factoring.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

inductive Instr where
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
  | EBREAK (address : BitVec 64)
  | FENCE
  | ADD  (dst : Dst) (lhs rhs : Src)
  | SUB  (dst : Dst) (lhs rhs : Src)
  | MUL  (dst : Dst) (lhs rhs : Src)
  | MULH (dst : Dst) (lhs rhs : Src)
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
  | SLLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRAI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SLL  (dst : Dst) (value shamt : Src)
  | SRL  (dst : Dst) (value shamt : Src)
  | VirtualSignExtendWord (dst : Dst) (src : Src)
  | VirtualZeroExtendWord (dst : Dst) (src : Src)
  | VirtualMovsign (dst : Dst) (src : Src)
  | VirtualAssertHalfwordAlignment (base : regidx) (imm : BitVec 12)
  | VirtualAssertWordAlignment (base : regidx) (imm : BitVec 12)
  | VirtualAssertLoadAlignment (base : regidx) (imm : BitVec 12) (mask : BitVec 64)
  | VirtualAssertStoreAlignment (base : regidx) (imm : BitVec 12) (mask : BitVec 64)
  | LD (vd base : VReg) (imm : BitVec 12)
  | LDFrom (vd : VReg) (base : Src) (imm : BitVec 12)
  | SD (base value : VReg) (imm : BitVec 12)
  | SDFrom (base value : Src) (imm : BitVec 12)
  | VirtualLW (dst : Dst) (base : Src) (imm : BitVec 12)
  | VirtualSW (base value : Src) (imm : BitVec 12)
  | VirtualAdvice (vd : VReg) (value : BitVec 64)
  | VirtualAdviceLoad (dst : Dst) (value : BitVec 64)
  | VirtualAdviceLen (dst : Dst) (remaining : BitVec 64)
  | VirtualHostIO
  | VirtualAssertEQ (lhs rhs : VReg)
  | VirtualAssertEQReal (lhs : VReg) (rhs : regidx)
  | VirtualAssertValidDiv0 (divisor : regidx) (quotient : VReg)
  | VirtualAssertValidDiv0V (divisor quotient : VReg)
  | VirtualChangeDivisor (dst : VReg) (dividend divisor : regidx)
  | VirtualChangeDivisorW (dst dividend divisor : VReg)
  | VirtualAssertValidUnsignedRemainderReal (remainder : VReg) (divisor : regidx)
  | VirtualAssertValidUnsignedRemainder (remainder divisor : VReg)
  | VirtualAssertMulUNoOverflow (lhs : VReg) (rhs : regidx)
  | VirtualAssertMulUNoOverflowV (lhs rhs : VReg)
  | VirtualAssertLTEReal (lhs : VReg) (rhs : regidx)
  | VirtualAssertLTE (lhs rhs : VReg)
  deriving Repr

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
program.  This is useful for expansions such as `MULH`, which have no explicit
early-return instruction apart from the generic non-retire short-circuiting
handled by `Program.instr`. -/
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

end JoltISA
