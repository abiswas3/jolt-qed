import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Rust: crates/jolt-witness/src/backend/trace/oracle.rs::oracle_table.
-- Rust: crates/jolt-program/src/execution/trace.rs::JoltProgram::trace_with and TraceInputs.
-- ISA: JoltBytecode/JoltISA/Core.lean::SailJoltState.
-- TODO: Eventually name it params and not p but its not a major issue for now
noncomputable def JoltProgram.honestWitness {F : Type} [Field F] (p : WitnessParams)
    (program : JoltProgram) (initialState : SailJoltState)
    (succeeds : (program.execute initialState p.traceLength).isOk = true) : WitnessType F p :=
  let executionTrace :=
    match result : program.execute initialState p.traceLength with
    | .ok rows => rows
    | .error _ => False.elim (by simp [result, Except.isOk, Except.toBool] at succeeds)
  {
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
    ShouldBranch := HonestWitness.ShouldBranch p program executionTrace
    ShouldJump := HonestWitness.ShouldJump p program initialState
    NextUnexpandedPC := HonestWitness.NextUnexpandedPC p program initialState
    NextPC := HonestWitness.NextPC p program initialState
    NextIsVirtual := HonestWitness.NextIsVirtual p program initialState
    NextIsFirstInSequence := HonestWitness.NextIsFirstInSequence p program initialState
    NextIsNoop := HonestWitness.NextIsNoop p program initialState
    OpFlags := HonestWitness.OpFlags p program executionTrace
    InstructionFlags := HonestWitness.InstructionFlags p program executionTrace
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
    InstructionRa := HonestWitness.InstructionRa p program initialState }
