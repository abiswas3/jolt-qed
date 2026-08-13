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

/-- Index of the machine state immediately before row `i`. -/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- Index of the machine state immediately after row `i`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

/-- A destination whose written value can be recovered from the post-state. -/
def DestinationRecorded : JoltISA.Dst → Prop
  | .vreg _ => True
  | .xreg rd => rd ≠ regidx.Regidx 0

/--
The final-trace row invariant currently needed by the constraint layer.

The real tracer replaces a pure-writeback `AND` or `ANDI` whose architectural
destination is `x0` by its `ADDI x0, x0, 0` no-op row. As more instruction
constraints are added, this predicate is where their corresponding final-row
conditions belong.
TODO: (2026-08-03) this is incomplete as we have just modelled AND so far.
We will have to likely change this to accomodate memory writes.
-/
def FinalTraceRow : JoltISA.Instr → Prop
  | .ANDI dst _ _ => DestinationRecorded dst
  | .AND dst _ _ => DestinationRecorded dst
  | _ => True

/--
An honest Jolt ISA trace.

The trace stores `T` instructions and `T + 1` states. The `executes` field says
that every adjacent pair of states is related by the existing Jolt ISA
semantics. No instruction semantics are restated in the constraint layer.
-/
structure HonestTrace (T : Nat) where
  instrList : Column T JoltISA.Instr
  state : Column (T + 1) SailJoltState
  executes : ∀ i : Fin T,
    (JoltISA.execInstr (instrList i)).run (state (currentStateIndex i)) =
      .ok RETIRE_SUCCESS (state (nextStateIndex i))
  /-- Every row satisfies the final-tracer facts currently modelled. -/
  finalRow : ∀ i : Fin T, FinalTraceRow (instrList i)

/-- State immediately before execution row `i`. -/
def HonestTrace.preState {T : Nat}
    (trace : HonestTrace T) (i : Fin T) : SailJoltState :=
  trace.state (currentStateIndex i)

/-- State immediately after execution row `i`. -/
def HonestTrace.postState {T : Nat}
    (trace : HonestTrace T) (i : Fin T) : SailJoltState :=
  trace.state (nextStateIndex i)

end JoltConstraints
