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

structure JoltTraceMetadata (params : JoltWitnessParams) where
  row : Column params.traceLength JoltTraceRowMetadata
  lowestMemoryAddress : BitVec Xlen
  trustedAdvice : Column params.trustedAdviceLength (BitVec Xlen)
  untrustedAdvice : Column params.untrustedAdviceLength (BitVec Xlen)

/-- Index of the machine state immediately before row `i`. -/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- Index of the machine state immediately after row `i`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

structure HonestTrace (params : JoltWitnessParams) where
  instrList : Column params.traceLength JoltISA.Instr
  state : Column (params.traceLength + 1) SailJoltState
  executes : ∀ i : Fin params.traceLength,
    (JoltISA.execInstr (instrList i)).run (state (currentStateIndex i)) = .ok RETIRE_SUCCESS (state (nextStateIndex i))
  metadata : JoltTraceMetadata params


/-- State immediately before execution row `i`. -/
def HonestTrace.preState {params : JoltWitnessParams}
    (trace : HonestTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (currentStateIndex i)

/-- State immediately after execution row `i`. -/
def HonestTrace.postState {params : JoltWitnessParams}
    (trace : HonestTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (nextStateIndex i)

end JoltConstraints
