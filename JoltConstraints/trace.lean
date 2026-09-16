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

-- Rust: tracer/src/emulator/cpu.rs::Cpu::{tick_operate, decode_and_cache}.
-- ISA: LeanRV64D/Step.lean::run_hart_active; JoltBytecode/JoltISA/Core.lean::liftSail.
noncomputable def JoltProgramRow.preparePC (row : JoltProgramRow) : JoltMonad Unit :=
  liftSail do
    Sail.writeReg Register.PC row.address
    Sail.writeReg Register.nextPC
      (row.address + if row.isCompressed then 2#64 else 4#64)

-- Rust: tracer/src/instruction/mod.rs::Instruction::execute.
-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr.
noncomputable def JoltProgramRow.execute (row : JoltProgramRow) :
    JoltMonad ExecutionResult := JoltISA.execInstr row.instruction

-- Rust: crates/jolt-program/src/execution/trace.rs::JoltProgram.
structure JoltProgram where
  -- Rust: JoltProgram::expanded_bytecode.
  expandedBytecode : Array JoltProgramRow
  -- Rust: JoltProgram::memory_init.
  memoryInit : Array (BitVec 64 × BitVec 8)
  -- Rust: JoltProgram::entry_address.
  entryAddress : BitVec 64

-- Rust: crates/jolt-program/src/preprocess/bytecode.rs::BytecodePCMapper::get_first_pc.
-- TODO: Relate this unpadded row index to Rust's padded bytecode PC.
-- The index/offset of the program entry address. We could have no ops in the program.
def JoltProgram.entryRowIndex (program : JoltProgram) :
    Option (Fin program.expandedBytecode.size) :=
  program.expandedBytecode.findFinIdx? (fun row => row.address == program.entryAddress)

-- Rust: crates/jolt-program/src/execution/trace.rs::TraceRow.
-- ISA: JoltBytecode/JoltISA/Core.lean::SailJoltState and JoltMonad.
structure JoltTraceRow where
  -- Rust: TraceRow::instruction.
  programRow : JoltProgramRow
  -- Rust: RegisterRead::value, RegisterWrite::pre_value, RamRead::value, RamWrite::pre_value.
  preState : SailJoltState
  -- Rust: RegisterWrite::post_value and RamWrite::post_value; ISA: JoltMonad's full result.
  outcome : EStateM.Result (Sail.Error exception) SailJoltState ExecutionResult

-- Rust: tracer/src/emulator/cpu.rs::Cpu::tick_operate; tracer/src/trace_row.rs::cycle_to_trace_row.
-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr, via JoltProgramRow.execute.
noncomputable def JoltProgramRow.executeAndRecord
    (row : JoltProgramRow) (state : SailJoltState) : JoltTraceRow :=
  match row.preparePC state with
  | .ok _ preState =>
      { programRow := row
        preState := preState
        outcome := row.execute preState }
  | .error error preState =>
      { programRow := row
        preState := preState
        outcome := .error error preState }

-- Rust: tracer/src/instruction/mod.rs::trace_inline_sequence.
-- Rust: crates/jolt-program/src/preprocess/bytecode.rs::BytecodePCMapper::{validate_run, get_first_pc}.
-- ISA: LeanRV64D/PcAccess.lean::get_next_pc.
-- TODO: Validate expanded-bytecode virtual-sequence metadata.
noncomputable def JoltProgram.nextRowIndex
    (program : JoltProgram) (currentIndex : Fin program.expandedBytecode.size) :
    JoltMonad (Option (Fin program.expandedBytecode.size)) := do
  let row := program.expandedBytecode[currentIndex]
  if row.virtualSequenceRemaining.getD 0#16 != 0#16 then
    if h : currentIndex.val + 1 < program.expandedBytecode.size then
      pure (some ⟨currentIndex.val + 1, h⟩)
    else
      pure none
  else
    let nextAddress ← liftSail (LeanRV64D.Functions.get_next_pc ())
    pure (program.expandedBytecode.findFinIdx? (fun row => row.address == nextAddress))
