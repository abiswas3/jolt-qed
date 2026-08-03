import JoltBytecode.JoltISA.Semantics

open Sail PreSail LeanRV64D.Functions

/-!
# Shared definitions for Jolt constraints

Only definitions that are shared by more than one constraint belong here.
The power-of-two trace domain and polynomial/sum-check layer will be added when
they are actually used.
-/

namespace JoltConstraints

universe u

/-- A trace column with one value at each of `T` rows. -/
abbrev Column (T : Nat) (α : Type u) : Type u :=
  Fin T → α

/-- Register width of the current Jolt ISA model. -/
abbrev Xlen : Nat := 64

/-- The trace length assumption needed by the later sum-check layer. -/
def IsPowerOfTwo (T : Nat) : Prop :=
  ∃ n : Nat, T = 2 ^ n

/-- State index at the beginning of execution row `i`. -/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- State index immediately after execution row `i`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

/--
A dynamic execution trace has `T` instructions and `T + 1` machine states.
-/
structure ExecutionTrace (T : Nat) where
  instr : Column T JoltISA.Instr
  state : Column (T + 1) SailJoltState

def ExecutionTrace.preState {T : Nat}
    (trace : ExecutionTrace T) (i : Fin T) : SailJoltState :=
  trace.state (currentStateIndex i)

def ExecutionTrace.postState {T : Nat}
    (trace : ExecutionTrace T) (i : Fin T) : SailJoltState :=
  trace.state (nextStateIndex i)

/-- One successful step according to the existing JoltISA semantics. -/
def InstructionStep
    (instr : JoltISA.Instr) (preState postState : SailJoltState) : Prop :=
  (JoltISA.execInstr instr).run preState =
    .ok RETIRE_SUCCESS postState

/-- Every row follows the existing `JoltISA.execInstr` semantics. -/
def ExecutionTrace.Executes {T : Nat} (trace : ExecutionTrace T) : Prop :=
  ∀ i : Fin T,
    InstructionStep
      (trace.instr i)
      (trace.preState i)
      (trace.postState i)

end JoltConstraints
