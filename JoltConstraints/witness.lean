import Mathlib.Algebra.Field.Defs
import JoltConstraints.basic_new
import JoltConstraints.trace

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

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch.
noncomputable def ShouldBranch [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldJump.
noncomputable def ShouldJump [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextUnexpandedPc.
noncomputable def NextUnexpandedPC [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

-- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextPc.
noncomputable def NextPC [Field F] (_program : JoltProgram)
    (_initialState : SailJoltState) : Fin p.traceLength → F := by
  sorry

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

end HonestWitness

-- Rust: crates/jolt-witness/src/backend/trace/oracle.rs::oracle_table.
-- Rust: crates/jolt-program/src/execution/trace.rs::JoltProgram::trace_with and TraceInputs.
-- ISA: JoltBytecode/JoltISA/Core.lean::SailJoltState.
-- TODO: Eventually name it params and not p but its not a major issue for now
noncomputable def JoltProgram.honestWitness {F : Type} [Field F] (p : WitnessParams)
    (program : JoltProgram) (initialState : SailJoltState) : WitnessType F p where
  PC := HonestWitness.PC p program initialState
  UnexpandedPC := HonestWitness.UnexpandedPC p program initialState
  Imm := HonestWitness.Imm p program initialState
  Rs1Value := HonestWitness.Rs1Value p program initialState
  Rs2Value := HonestWitness.Rs2Value p program initialState
  RdWriteValue := HonestWitness.RdWriteValue p program initialState
  RamAddress := HonestWitness.RamAddress p program initialState
  RamReadValue := HonestWitness.RamReadValue p program initialState
  RamWriteValue := HonestWitness.RamWriteValue p program initialState
  LeftInstructionInput := HonestWitness.LeftInstructionInput p program initialState
  RightInstructionInput := HonestWitness.RightInstructionInput p program initialState
  LeftLookupOperand := HonestWitness.LeftLookupOperand p program initialState
  RightLookupOperand := HonestWitness.RightLookupOperand p program initialState
  LookupOutput := HonestWitness.LookupOutput p program initialState
  Product := HonestWitness.Product p program initialState
  ShouldBranch := HonestWitness.ShouldBranch p program initialState
  ShouldJump := HonestWitness.ShouldJump p program initialState
  NextUnexpandedPC := HonestWitness.NextUnexpandedPC p program initialState
  NextPC := HonestWitness.NextPC p program initialState
  NextIsVirtual := HonestWitness.NextIsVirtual p program initialState
  NextIsFirstInSequence := HonestWitness.NextIsFirstInSequence p program initialState
  NextIsNoop := HonestWitness.NextIsNoop p program initialState
  OpFlags := HonestWitness.OpFlags p program initialState
  InstructionFlags := HonestWitness.InstructionFlags p program initialState
  LookupTableFlag := HonestWitness.LookupTableFlag p program initialState
  InstructionRafFlag := HonestWitness.InstructionRafFlag p program initialState
  RdInc := HonestWitness.RdInc p program initialState
  RamInc := HonestWitness.RamInc p program initialState
  RamHammingWeight := HonestWitness.RamHammingWeight p program initialState
  Rs1Ra := HonestWitness.Rs1Ra p program initialState
  Rs2Ra := HonestWitness.Rs2Ra p program initialState
  RdWa := HonestWitness.RdWa p program initialState
  RegistersVal := HonestWitness.RegistersVal p program initialState
  RamRa := HonestWitness.RamRa p program initialState
  RamVal := HonestWitness.RamVal p program initialState
  RamValFinal := HonestWitness.RamValFinal p program initialState
  InstructionRaChunk := HonestWitness.InstructionRaChunk p program initialState
  BytecodeRaChunk := HonestWitness.BytecodeRaChunk p program initialState
  RamRaChunk := HonestWitness.RamRaChunk p program initialState
  InstructionRa := HonestWitness.InstructionRa p program initialState
