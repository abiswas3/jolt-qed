import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

open LeanRV64D.Functions

namespace JoltISA

-- Rust: tracer/src/instruction/{beq,bne,blt,bge,bltu,bgeu}.rs::exec.
-- Rust: crates/jolt-lookup-tables/src/instructions/riscv/{beq,bne,blt,bge,bltu,bgeu}.rs::to_lookup_output.
/-- Based on the contents of the decision we make a decision -/
noncomputable def branchDecision (instruction : Instr) : JoltMonad Bool :=
  match instruction with
  | .BEQ lhs rhs _ => do
      return (← readSrc lhs) == (← readSrc rhs)
  | .BNE lhs rhs _ => do
      return (← readSrc lhs) != (← readSrc rhs)
  | .BLT lhs rhs _ => do
      return zopz0zI_s (← readSrc lhs) (← readSrc rhs)
  | .BGE lhs rhs _ => do
      return zopz0zKzJ_s (← readSrc lhs) (← readSrc rhs)
  | .BLTU lhs rhs _ => do
      return zopz0zI_u (← readSrc lhs) (← readSrc rhs)
  | .BGEU lhs rhs _ => do
      return zopz0zKzJ_u (← readSrc lhs) (← readSrc rhs)
  | _ => pure false

end JoltISA
