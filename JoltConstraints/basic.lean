import JoltBytecode.JoltISA.Semantics

/-!
# Core objects for constraint sketches

These are deliberately lightweight Lean models of the columns we eventually
want to turn into polynomial witnesses.  The constraint-specific statements
live in separate files.
-/

namespace JoltConstraints

universe u

/-- A trace column with one value per row. -/
abbrev Column (T : Nat) (alpha : Type u) : Type u :=
  Fin T -> alpha

/-- We keep the power-of-two condition separate from the column definition. -/
def IsPowerOfTwo (T : Nat) : Prop :=
  exists k : Nat, T = 2 ^ k

/-- RV64 machine words. -/
abbrev Word : Type :=
  BitVec 64

/-- The final Jolt instruction at each row. -/
abbrev InstrTrace (T : Nat) : Type :=
  Column T JoltISA.Instr

/-- A Boolean selector column.  Later this can become a field-valued column. -/
abbrev FlagColumn (T : Nat) : Type :=
  Column T Bool

/-- State index for the beginning of row `i`. -/
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

/-- The opcode selector fragment of the witness. -/
structure Witness (T : Nat) where
  AND_FLAG : FlagColumn T

/-- The predicate "this instruction is some `JoltISA.Instr.AND`". -/
def IsANDInstr (instr : JoltISA.Instr) : Prop :=
  exists (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    instr = JoltISA.Instr.AND rd rs1 rs2

/--
Soundness of `AND_FLAG`: an active flag determines that the row instruction is
an AND instruction.  The theorem in `and_constraint.lean` uses this implication
as its entry point.
-/
def AND_FlagSound {T : Nat} (w : Witness T) (trace : CpuTrace T) : Prop :=
  forall i : Fin T, w.AND_FLAG i = true -> IsANDInstr (trace.instr i)

/-- A pair of 64-bit words is encoded as one 128-bit lookup-table row key. -/
abbrev AND_LookupKey : Type :=
  BitVec 128

/--
The fixed AND lookup table.

Conceptually this is a vector of length `2^128`; row `a || b` stores `a &&& b`.
We use `Column (2^128)` so Lean treats the row index as `Fin (2^128)`.
-/
structure AND_LookupTable where
  value : Column (2 ^ 128) Word

/-- The lookup-table row key for operands `a` and `b`. -/
def andLookupKey (a b : Word) : AND_LookupKey :=
  a +++ b

/-- The finite table row corresponding to key `a || b`. -/
def andLookupRow (a b : Word) : Fin (2 ^ 128) :=
  (andLookupKey a b).toFin

/--
Per-row operand values used by the AND lookup.

On an active AND row, these should be exactly the values obtained by JoltISA's
monadic reads of `rs1` and `rs2`.
-/
structure AND_LookupWitness (T : Nat) where
  rs1Val : Column T Word
  rs2Val : Column T Word

/--
The per-row destination-register value table.

`RDVal i` is intended to be the value written to the destination register by
row `i`.
-/
structure RDValueTable (T : Nat) where
  RDVal : Column T Word

end JoltConstraints
