import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::Pc.
noncomputable def PC [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::UnexpandedPc.
noncomputable def UnexpandedPC [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::Imm.
noncomputable def Imm [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/registers.rs::Rs1Value.
noncomputable def Rs1Value [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/registers.rs::Rs2Value.
noncomputable def Rs2Value [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/registers.rs::RdWriteValue.
noncomputable def RdWriteValue [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamAddress.
noncomputable def RamAddress [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamReadValue.
noncomputable def RamReadValue [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamWriteValue.
noncomputable def RamWriteValue [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::LeftInstructionInput.
noncomputable def LeftInstructionInput [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::RightInstructionInput.
noncomputable def RightInstructionInput [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::LeftLookupOperand.
noncomputable def LeftLookupOperand [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::RightLookupOperand.
noncomputable def RightLookupOperand [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/lookups.rs::LookupOutput.
noncomputable def LookupOutput [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/operands.rs::Product.
noncomputable def Product [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldJump.
noncomputable def ShouldJump [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextUnexpandedPc.
noncomputable def NextUnexpandedPC [Field F] (program : JoltProgram)
    (initialState : SailJoltState) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      UnexpandedPC p program initialState ⟨t.val + 1, nextInBounds⟩
    else 0

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextPc.
noncomputable def NextPC [Field F] (program : JoltProgram)
    (initialState : SailJoltState) : Fin p.traceLength → F :=
  fun t =>
    if nextInBounds : t.val + 1 < p.traceLength then
      PC p program initialState ⟨t.val + 1, nextInBounds⟩
    else 0

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsVirtual.
noncomputable def NextIsVirtual [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsFirstInSequence.
noncomputable def NextIsFirstInSequence [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsNoop.
noncomputable def NextIsNoop [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::OpFlag.
noncomputable def OpFlags [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : CircuitFlags → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionFlag.
noncomputable def InstructionFlags [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : _root_.InstructionFlags → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::LookupTableFlag.
noncomputable def LookupTableFlag [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : LookupTableKind → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionRafFlag.
noncomputable def InstructionRafFlag [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/increments.rs::RdInc.
noncomputable def RdInc [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/increments.rs::RamInc.
noncomputable def RamInc [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamHammingWeight.
noncomputable def RamHammingWeight [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
-- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
noncomputable def Rs1Ra [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin 128 → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
-- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
noncomputable def Rs2Ra [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin 128 → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
-- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
noncomputable def RdWa [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin 128 → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
-- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
noncomputable def RegistersVal [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin 128 → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_ra.
noncomputable def RamRa [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.ramSize → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_val.
noncomputable def RamVal [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.ramSize → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_val_final.
noncomputable def RamValFinal [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.ramSize → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::InstructionRaChunk.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
noncomputable def InstructionRaChunk [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) :
    Fin p.instructionChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::BytecodeRaChunk.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
noncomputable def BytecodeRaChunk [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) :
    Fin p.bytecodeChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::RamRaChunk.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
noncomputable def RamRaChunk [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) :
    Fin p.ramChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/backend/trace/oracle.rs::oracle_table (InstructionRa).
noncomputable def InstructionRa [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) :
    Fin p.virtualInstructionChunks → Fin (2 ^ p.virtualChunkBits) → Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-lookup-tables/src/instructions/riscv/{beq,bne,blt,bge,bltu,bgeu}.rs::to_lookup_output.
-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr uses these same operand reads and comparisons.
noncomputable def branchDecision (instruction : JoltISA.Instr) : JoltMonad Bool :=
  match instruction with
  | .BEQ lhs rhs _ => do
      return (← JoltISA.readSrc lhs) == (← JoltISA.readSrc rhs)
  | .BNE lhs rhs _ => do
      return (← JoltISA.readSrc lhs) != (← JoltISA.readSrc rhs)
  | .BLT lhs rhs _ => do
      return LeanRV64D.Functions.zopz0zI_s (← JoltISA.readSrc lhs) (← JoltISA.readSrc rhs)
  | .BGE lhs rhs _ => do
      return LeanRV64D.Functions.zopz0zKzJ_s (← JoltISA.readSrc lhs) (← JoltISA.readSrc rhs)
  | .BLTU lhs rhs _ => do
      return LeanRV64D.Functions.zopz0zI_u (← JoltISA.readSrc lhs) (← JoltISA.readSrc rhs)
  | .BGEU lhs rhs _ => do
      return LeanRV64D.Functions.zopz0zKzJ_u (← JoltISA.readSrc lhs) (← JoltISA.readSrc rhs)
  | _ => pure false

-- ISA: JoltBytecode/JoltISA/Semantics.lean::execInstr propagates branch-operand read failures.
theorem branchDecision_error (instruction : JoltISA.Instr) (preState postState : SailJoltState)
    (error : Sail.Error exception)
    (failed : branchDecision instruction preState = .error error postState) :
    JoltISA.execInstr instruction preState = .error error postState := by
  cases instruction <;>
    simp [branchDecision, bind, EStateM.bind, pure, EStateM.pure] at failed
  all_goals
    simp only [JoltISA.execInstr, bind, EStateM.bind]
    split at failed
    · split at failed
      · cases failed
      · cases failed
        rfl
    · cases failed
      rfl

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch::{extract, to_field}.
noncomputable def ShouldBranch [Field F] (program : JoltProgram)
    (executionTrace : Array (JoltTraceRow program)) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < executionTrace.size then
      let row := executionTrace[t.val]
      match decision : branchDecision program.expandedBytecode[row.rowIndex].instruction row.preState with
      | .ok taken _ => if taken then 1 else 0
      | .error error state => False.elim (by
          have failed := branchDecision_error _ _ state error decision
          rw [row.executes] at failed
          cases failed)
    else 0

end HonestWitness
