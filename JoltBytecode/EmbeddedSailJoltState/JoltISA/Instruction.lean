import JoltBytecode.EmbeddedSailJoltState.JoltISA.Values

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
  | LUI  (dst : Dst) (imm : BitVec 64)
  | AUIPC (dst : Dst) (imm : BitVec 20)
  | JAL (dst : Dst) (imm : BitVec 21)
  | JALR (dst : Dst) (base : Src) (imm : BitVec 12)
  | ADD  (dst : Dst) (lhs rhs : Src)
  | SUB  (dst : Dst) (lhs rhs : Src)
  | MUL  (dst : Dst) (lhs rhs : Src)
  | MULH (dst : Dst) (lhs rhs : Src)
  | MULHU (dst : Dst) (lhs rhs : Src)
  | VirtualMULI (dst : Dst) (src : Src) (imm : BitVec 64)
  | VirtualPow2 (dst : Dst) (src : Src)
  | VirtualPow2W (dst : Dst) (src : Src)
  | VirtualShiftRightBitmask (dst : Dst) (src : Src)
  | VirtualSRLI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRAI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRL (dst : Dst) (value bitmask : Src)
  | VirtualSRA (dst : Dst) (value bitmask : Src)
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
  | SExtW (dst : Dst) (src : Src)
  | ZExtW (dst : Dst) (src : Src)
  | Movsign (dst : Dst) (src : Src)
  | AssertLoadAlign (base : regidx) (imm : BitVec 12) (mask : BitVec 64)
  | AssertStoreAlign (base : regidx) (imm : BitVec 12) (mask : BitVec 64)
  | LD (vd base : VReg) (imm : BitVec 12)
  | LDFrom (vd : VReg) (base : Src) (imm : BitVec 12)
  | SD (base value : VReg) (imm : BitVec 12)
  | SDFrom (base value : Src) (imm : BitVec 12)
  | Advice (vd : VReg) (value : BitVec 64)
  | AssertEq (lhs rhs : VReg)
  | AssertEqReal (lhs : VReg) (rhs : regidx)
  | AssertValidDiv0 (divisor : regidx) (quotient : VReg)
  | AssertValidDiv0V (divisor quotient : VReg)
  | ChangeDivisor (dst : VReg) (dividend divisor : regidx)
  | ChangeDivisorW (dst dividend divisor : VReg)
  | AssertValidUnsignedRemainderReal (remainder : VReg) (divisor : regidx)
  | AssertValidUnsignedRemainder (remainder divisor : VReg)
  | AssertMulUNoOverflow (lhs : VReg) (rhs : regidx)
  | AssertMulUNoOverflowV (lhs rhs : VReg)
  | AssertLTEReal (lhs : VReg) (rhs : regidx)
  | AssertLTE (lhs rhs : VReg)
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

end JoltISA
