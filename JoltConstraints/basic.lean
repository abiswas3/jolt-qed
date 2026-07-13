import JoltBytecode.JoltISA.Semantics

/-!
# Core objects for constraint sketches

These are deliberately lightweight Lean models of the columns we eventually
want to turn into polynomial witnesses.  Constraint-specific statements live in
separate files.
-/

namespace JoltConstraints

universe u

/-- A trace column with one value per row. 
Here 
T: represents the time step 
alpha: Is a type (Like ℝ, ℕ, or some inductive type JoltISA.instr
-/
abbrev Column (T : Nat) (alpha : Type u) : Type u :=
  Fin T -> alpha

/-- We keep the power-of-two condition separate from the column definition. -/
def IsPowerOfTwo (T : Nat) : Prop :=
  exists k : Nat, T = 2 ^ k

/-- The register width for the RV64 Jolt model. -/
abbrev Xlen : Nat := 64

/-- The final Jolt instruction at each row. -/
abbrev InstrTrace (T : Nat) : Type :=
  Column T JoltISA.Instr

/-- A selector column over the algebraic domain used by the constraints. -/
abbrev FlagColumn (T : Nat) (F : Type u) : Type u :=
  Column T F

/-- 
  If there are T instruction steps, then there are:
  state[i] = state after instruction [i-1]
  state[0] = initial state.
  T instructions:           instr[0], ..., instr[T-1]
  T+1 states:      state[0], ...,  ...,    state[T]

Each instruction consumes one state and produces the next:
State index for the beginning of row `i`. 
-/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- State index for the end of row `i`, equivalently the start of row `i + 1`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- The semantic trace columns that constraints should justify. -/
structure CpuTrace (T : Nat) where
  instr : InstrTrace T
  state : Column (T + 1) SailJoltState

/-- The pre-state for row `i`. -/
def rowPreState {T : Nat} (trace : CpuTrace T) (i : Fin T) : SailJoltState :=
  trace.state (currentStateIndex i)

/-- The post-state slot for row `i`. -/
def rowPostState {T : Nat} (trace : CpuTrace T) (i : Fin T) : SailJoltState :=
  trace.state (nextStateIndex i)

end JoltConstraints
