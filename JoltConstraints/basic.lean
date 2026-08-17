import JoltBytecode.JoltISA.Semantics

/-!
# Jolt ISA execution traces

This file contains only the semantic trace used by the constraint layer.
Correct execution is defined exclusively by the existing `JoltISA.execInstr`.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltConstraints

universe u

/-- A column with one value at each of `T` trace rows. -/
abbrev Column (T : Nat) (α : Type u) : Type u :=
  Fin T → α

/-- Register width of the current Jolt ISA. -/
abbrev Xlen : Nat := 64

structure JoltWitnessParams where
  logT : Nat
  ramK : Nat
  bytecodeK : Nat
  committedChunkBits : Nat
  lookupVirtualChunkBits : Nat
  includeTrustedAdvice : Bool
  includeUntrustedAdvice : Bool
  maxTrustedAdviceSize : Nat
  maxUntrustedAdviceSize : Nat
  deriving DecidableEq, Repr

namespace JoltWitnessParams

def traceLength (params : JoltWitnessParams) : Nat :=
  2 ^ params.logT

def ceilDiv (n d : Nat) : Nat :=
  (n + d - 1) / d

def committedChunkSize (params : JoltWitnessParams) : Nat :=
  2 ^ params.committedChunkBits

def lookupVirtualChunkSize (params : JoltWitnessParams) : Nat :=
  2 ^ params.lookupVirtualChunkBits

def instructionCommittedRaCount (params : JoltWitnessParams) : Nat :=
  ceilDiv (2 * Xlen) params.committedChunkBits

def bytecodeCommittedRaCount (params : JoltWitnessParams) : Nat :=
  ceilDiv (Nat.clog 2 params.bytecodeK) params.committedChunkBits

def ramCommittedRaCount (params : JoltWitnessParams) : Nat :=
  ceilDiv (Nat.clog 2 params.ramK) params.committedChunkBits

def instructionVirtualRaCount (params : JoltWitnessParams) : Nat :=
  (2 * Xlen) / params.lookupVirtualChunkBits

def adviceLength (maxSizeBytes : Nat) : Nat :=
  max 1 (Nat.nextPowerOfTwo (maxSizeBytes / 8))

def trustedAdviceLength (params : JoltWitnessParams) : Nat :=
  adviceLength params.maxTrustedAdviceSize

def untrustedAdviceLength (params : JoltWitnessParams) : Nat :=
  adviceLength params.maxUntrustedAdviceSize

end JoltWitnessParams

structure JoltTraceRowMetadata where
  pc : Nat
  unexpandedPC : BitVec Xlen
  virtualSequenceRemaining : Option Nat
  isFirstInSequence : Bool
  isCompressed : Bool

/-- The three mutually exclusive row classes used by Rust's proof-facing
`JoltTraceRow`. -/
inductive JoltTraceRowClass where
  | nonMemory
  | load
  | store
  deriving DecidableEq, Repr

/-- Classify a final Jolt instruction exactly as Rust classifies its captured
state before constructing a proof-facing trace row. -/
def JoltTraceRowClass.ofInstr : JoltISA.Instr → JoltTraceRowClass
  | .LD .. => .load
  | .SD .. => .store
  | _ => .nonMemory

/-- Independent witness values stored for a non-memory row. -/
structure NonMemoryState where
  rs1Value : BitVec Xlen
  rs2Value : BitVec Xlen
  rdPreValue : BitVec Xlen
  rdWriteValue : BitVec Xlen
  deriving Repr

/-- Independent witness values stored for a load row.  As in Rust,
`rdWriteValue` is also the logical RAM read and RAM write value. -/
structure LoadState where
  rs1Value : BitVec Xlen
  ramAddress : BitVec Xlen
  rdPreValue : BitVec Xlen
  rdWriteValue : BitVec Xlen
  deriving Repr

/-- Independent witness values stored for a store row.  As in Rust,
`rs2Value` is also the logical RAM write value. -/
structure StoreState where
  rs1Value : BitVec Xlen
  rs2Value : BitVec Xlen
  ramReadValue : BitVec Xlen
  ramAddress : BitVec Xlen
  deriving Repr

/-- Rust's `CapturedState`, indexed in Lean by the final row class.  The index
is the type-level counterpart of Rust's checked `from_components` constructor:
a load instruction cannot be paired with non-memory or store values. -/
inductive CapturedState : JoltTraceRowClass → Type where
  | nonMemory (state : NonMemoryState) : CapturedState .nonMemory
  | load (state : LoadState) : CapturedState .load
  | store (state : StoreState) : CapturedState .store

/-- The logical proof-facing trace row.  Rust packs this information into 64
bytes; Lean keeps the semantic components explicit. -/
structure JoltTraceRow where
  instruction : JoltISA.Instr
  metadata : JoltTraceRowMetadata
  capturedState : CapturedState (JoltTraceRowClass.ofInstr instruction)

namespace CapturedState

def rs1Value {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rs1Value
  | .load state => state.rs1Value
  | .store state => state.rs1Value

def rs2Value {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rs2Value
  | .load _ => 0
  | .store state => state.rs2Value

def rdPreValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rdPreValue
  | .load state => state.rdPreValue
  | .store _ => 0

def rdWriteValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rdWriteValue
  | .load state => state.rdWriteValue
  | .store _ => 0

def ramAddress {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.ramAddress
  | .store state => state.ramAddress

def ramReadValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.rdWriteValue
  | .store state => state.ramReadValue

def ramWriteValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.rdWriteValue
  | .store state => state.rs2Value

end CapturedState

namespace JoltTraceRow

def rs1Value (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rs1Value

def rs2Value (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rs2Value

def rdPreValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rdPreValue

def rdWriteValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rdWriteValue

def ramAddress (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramAddress

def ramReadValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramReadValue

def ramWriteValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramWriteValue

end JoltTraceRow

structure JoltTraceMetadata (params : JoltWitnessParams) where
  lowestMemoryAddress : BitVec Xlen
  trustedAdvice : Column params.trustedAdviceLength (BitVec Xlen)
  untrustedAdvice : Column params.untrustedAdviceLength (BitVec Xlen)

/-- Index of the machine state immediately before row `i`. -/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- Index of the machine state immediately after row `i`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

structure ExecutionTrace (params : JoltWitnessParams) where
  rows : Column params.traceLength JoltTraceRow
  state : Column (params.traceLength + 1) SailJoltState
  executes : ∀ i : Fin params.traceLength,
    (JoltISA.execInstr (rows i).instruction).run (state (currentStateIndex i)) =
      .ok RETIRE_SUCCESS (state (nextStateIndex i))
  metadata : JoltTraceMetadata params

/-- The final instruction column, derived from the proof-facing rows. -/
def ExecutionTrace.instrList {params : JoltWitnessParams}
    (trace : ExecutionTrace params) : Column params.traceLength JoltISA.Instr :=
  fun i => (trace.rows i).instruction

/-- Per-row instruction metadata, derived from the proof-facing rows. -/
def ExecutionTrace.rowMetadata {params : JoltWitnessParams}
    (trace : ExecutionTrace params) : Column params.traceLength JoltTraceRowMetadata :=
  fun i => (trace.rows i).metadata


/-- State immediately before execution row `i`. -/
def ExecutionTrace.preState {params : JoltWitnessParams}
    (trace : ExecutionTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (currentStateIndex i)

/-- State immediately after execution row `i`. -/
def ExecutionTrace.postState {params : JoltWitnessParams}
    (trace : ExecutionTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (nextStateIndex i)

end JoltConstraints
