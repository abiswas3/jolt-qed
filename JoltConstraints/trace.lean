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

-- Rust: crates/jolt-program/src/preprocess/bytecode.rs::BytecodePCMapper::{try_new, validate_run,
-- try_get_index}; crates/jolt-program/src/expand/metadata.rs::stamp_sequence_metadata;
-- common/src/constants.rs::{RAM_START_ADDRESS, ALIGNMENT_FACTOR_BYTECODE}.
-- TODO: is legal valid code, we will get to this later.
def JoltProgram.validateBytecode (program : JoltProgram) : Except JoltTraceError Unit := do
  let mut seen : List (BitVec 64) := []
  let mut expected : Option (BitVec 64 × Nat) := none
  for rowIndex in Array.finRange program.expandedBytecode.size do
    let row := program.expandedBytecode[rowIndex]
    if row.address.toNat < 0x80000000 || row.address.toNat % 2 != 0 then
      throw (.invalidBytecode rowIndex.val)
    match expected with
    | some (address, remaining) =>
        if row.address != address || row.isFirstInSequence ||
            row.virtualSequenceRemaining.map BitVec.toNat != some remaining then
          throw (.invalidBytecode rowIndex.val)
    | none =>
        if seen.contains row.address || row.isFirstInSequence !=
            row.virtualSequenceRemaining.isSome then
          throw (.invalidBytecode rowIndex.val)
        seen := row.address :: seen
    let remaining := (row.virtualSequenceRemaining.getD 0).toNat
    if remaining == 65535 || (remaining != 0 && row.isCompressed) then
      throw (.invalidBytecode rowIndex.val)
    expected := if remaining == 0 then none else some (row.address, remaining - 1)
  if expected.isSome then
    throw (.invalidBytecode (program.expandedBytecode.size - 1))

-- Rust: crates/jolt-program/src/preprocess/bytecode.rs::BytecodePCMapper::get_first_pc.
-- Lean indices refer to expandedBytecode before Rust's leading NoOp sentinel is added.
def JoltProgram.firstRowIndex (program : JoltProgram) (address : BitVec 64) :
    Except JoltTraceError (Fin program.expandedBytecode.size) :=
  match program.expandedBytecode.findFinIdx? (fun row => row.address == address) with
  | some rowIndex => .ok rowIndex
  | none => .error (.missingAddress address)

noncomputable section

-- Rust: tracer/src/emulator/cpu.rs::{tick_operate, decode_and_cache} advance PC once per source;
-- crates/jolt-program/src/expand/metadata.rs::stamp_sequence_metadata puts compression on the last row.
-- ISA: LeanRV64D/PcAccess.lean::{get_arch_pc, get_next_pc} use separate PC and nextPC registers.
def JoltProgram.prepareSourceState (program : JoltProgram)
    (rowIndex : Fin program.expandedBytecode.size) (state : SailJoltState) :
    Except JoltTraceError SailJoltState := do
  let row := program.expandedBytecode[rowIndex]
  let lastIndex := rowIndex.val + (row.virtualSequenceRemaining.getD 0).toNat
  if inBounds : lastIndex < program.expandedBytecode.size then
    let lastRow := program.expandedBytecode[lastIndex]
    let nextPC := row.address + if lastRow.isCompressed then 2 else 4
    return { state with sail := { state.sail with regs :=
      (state.sail.regs.insert Register.PC row.address).insert Register.nextPC nextPC } }
  else
    throw (.invalidBytecode rowIndex.val)

-- Rust: tracer/src/instruction/mod.rs::RISCVTrace::trace records state around instruction execution.
-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr is the sole instruction executor here.
def JoltProgram.executeRow (program : JoltProgram)
    (rowIndex : Fin program.expandedBytecode.size) (preState : SailJoltState) :
    Except JoltTraceError (JoltTraceRow program) :=
  match executed : JoltISA.execInstr program.expandedBytecode[rowIndex].instruction preState with
  | .ok (.Retire_Success ()) postState => .ok ⟨rowIndex, preState, postState, executed⟩
  | .ok result _ => .error (.notRetired rowIndex.val result)
  | .error error _ => .error (.isaError rowIndex.val error)

-- Rust: tracer/src/instruction/mod.rs::trace_inline_sequence runs expansion rows in order;
-- tracer/src/lib.rs::step_emulator stops on a stalled source PC, not a repeated virtual-row address.
-- The decreasing remainingSteps bound makes Lean recursion total; exhaustion is not termination.
def JoltProgram.executeFrom (program : JoltProgram) (remainingSteps : Nat)
    (rowIndex : Fin program.expandedBytecode.size) (preState : SailJoltState)
    (trace : Array (JoltTraceRow program)) : Except JoltTraceError (Array (JoltTraceRow program)) :=
  match remainingSteps with
  | 0 => .error (.stepLimit rowIndex.val)
  | steps + 1 => do
      let executed ← program.executeRow rowIndex preState
      let trace := trace.push executed
      let row := program.expandedBytecode[rowIndex]
      if (row.virtualSequenceRemaining.getD 0).toNat != 0 then
        if inBounds : rowIndex.val + 1 < program.expandedBytecode.size then
          program.executeFrom steps ⟨rowIndex.val + 1, inBounds⟩ executed.postState trace
        else
          throw (.invalidBytecode rowIndex.val)
      else
        match liftSail (LeanRV64D.Functions.get_next_pc ()) executed.postState with
        | .error error _ => throw (.isaError rowIndex.val error)
        | .ok nextAddress _ =>
            if nextAddress == row.address then
              return trace
            else
              let nextIndex ← program.firstRowIndex nextAddress
              let nextState ← program.prepareSourceState nextIndex executed.postState
              program.executeFrom steps nextIndex nextState trace

-- Rust: tracer/src/lib.rs::trace collects rows from the entry PC until step_emulator emits none.
-- Lean takes an already-initialized ISA state; memoryInit is not overlaid on the caller's memory.
-- ISA advice values are the values embedded in Instr, not Rust's per-execution advice patching.
def JoltProgram.execute (program : JoltProgram) (initialState : SailJoltState) (maxSteps : Nat) :
    Except JoltTraceError (Array (JoltTraceRow program)) := do
  program.validateBytecode
  let entryIndex ← program.firstRowIndex program.entryAddress
  let entryState ← program.prepareSourceState entryIndex initialState
  program.executeFrom maxSteps entryIndex entryState #[]

end
