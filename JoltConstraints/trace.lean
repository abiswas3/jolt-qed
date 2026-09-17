import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Semantics

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Rust: crates/jolt-riscv/src/row.rs::JoltInstructionRow.
structure JoltProgramRow where
  -- Rust: JoltInstructionRow::instruction_kind and operands; ISA: JoltBytecode/JoltISA/Instruction.lean::Instr.
  instruction : JoltISA.Instr
  -- Rust: JoltInstructionRow::address (RV64 instruction byte address).
  address : BitVec 64
  -- Rust: JoltInstructionRow::virtual_sequence_remaining.
  virtualSequenceRemaining : Option (BitVec 16)
  -- Rust: JoltInstructionRow::is_first_in_sequence.
  isFirstInSequence : Bool
  -- Rust: JoltInstructionRow::is_compressed.
  isCompressed : Bool

-- Rust: crates/jolt-program/src/execution/trace.rs::JoltProgram.
structure JoltProgram where
  -- Rust: JoltProgram::expanded_bytecode.
  expandedBytecode : Array JoltProgramRow
  -- Rust: JoltProgram::memory_init.
  memoryInit : Array (BitVec 64 × BitVec 8)
  -- Rust: JoltProgram::entry_address.
  entryAddress : BitVec 64

-- Rust: tracer/src/instruction/format/format_r.rs::{capture_pre_execution_state,
-- capture_post_execution_state}; Lean retains full ISA states, not just captured operands.
structure JoltTraceRow (program : JoltProgram) where
  rowIndex : Fin program.expandedBytecode.size
  preState : SailJoltState
  postState : SailJoltState
  -- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr; this certificate is Lean-only.
  executes : JoltISA.execInstr program.expandedBytecode[rowIndex].instruction preState =
    .ok (.Retire_Success ()) postState

-- Rust: crates/jolt-program/src/execution/error.rs::TraceError separates failure from trace output.
-- These cases distinguish Lean bytecode validation, ISA failures and the explicit execution bound.
inductive JoltTraceError where
  | invalidBytecode (rowIndex : Nat)
  | missingAddress (address : BitVec 64)
  | stepLimit (rowIndex : Nat)
  | isaError (rowIndex : Nat) (error : Sail.Error exception)
  | notRetired (rowIndex : Nat) (result : ExecutionResult)
