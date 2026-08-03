import JoltConstraints.basic

/-!
# The necessary AND constraint

The file has three parts:

1. `JoltData` lists the initial subset of prover-supplied Jolt data structures;
2. the tracer maps an execution trace to those data structures;
3. `ANDConstraint` is the equation from `spec/jolt-constraints.md`;
4. `ANDConstraint_isNecessary` states that correct AND execution implies that
   the traced data satisfies the constraint.

No sufficiency claim is made here.
-/

namespace JoltConstraints

open scoped BigOperators

universe u

/-! ## Initial subset of the Jolt data structures -/

/-- `K = 2^128`, the number of possible AND lookup keys. -/
abbrev ANDTableSize : Nat := 2 ^ 128

/-- One lookup key is an index into the `2^128` table rows. -/
abbrev ANDLookupKey : Type := Fin ANDTableSize

/-- A lookup vector indexed by all 128-bit keys. -/
abbrev ANDLookupVector (F : Type u) : Type u :=
  ANDLookupKey → F

/-- The fixed field-valued lookup table `T_AND`. -/
abbrev ANDTable (F : Type u) : Type u :=
  ANDLookupVector F

/--
The initial subset of the prover-supplied Jolt data structures.

These fields record claims; their types alone do not establish that the claims
are true or that field-valued flags are Boolean. Later constraints will enforce
those facts.
-/
structure JoltData (T : Nat) (F : Type u) where
  /-- The instruction the prover claims was executed at row `i`. -/
  trace : Column T JoltISA.Instr
  /-- `AND_FLAG[i] = 1` means the prover claims `trace[i]` was an AND. -/
  AND_FLAG : Column T F
  /-- The encoded value the prover claims was written at row `i`. -/
  RD_val : Column T F
  /-- The prover's `T × 2^128` lookup-address matrix. -/
  ra : Column T (ANDLookupVector F)

/-- Whether an instruction is an AND instruction. -/
def isAND : JoltISA.Instr → Bool
  | .AND _ _ _ => true
  | _ => false

/-- The proposition asserted by setting `AND_FLAG[i]` to one. -/
def JoltData.ClaimsAND {T : Nat} {F : Type u} [One F]
    (data : JoltData T F) (i : Fin T) : Prop :=
  data.AND_FLAG i = 1

/-- The claimed AND flag is sound with respect to the claimed instruction trace. -/
def ANDFlagSound {T : Nat} {F : Type u} [One F]
    (data : JoltData T F) : Prop :=
  ∀ i : Fin T,
    data.ClaimsAND i → isAND (data.trace i) = true

/-! ## The constraint, stated literally -/

/--
The constraint from the specification:

`AND_FLAG[i] * (RD_val[i] - ∑ k, ra[i,k] * T_AND[k]) = 0`.
-/
def ANDConstraint {T : Nat} {F : Type u} [Field F]
    (data : JoltData T F) (T_AND : ANDTable F) : Prop :=
  ∀ i : Fin T,
    data.AND_FLAG i *
      (data.RD_val i -
        ∑ k : ANDLookupKey, data.ra i k * T_AND k) = 0

/-! ## Trace to AND data structures -/

/-- The table key obtained by concatenating the two 64-bit operands. -/
def andLookupKey (a b : BitVec Xlen) : ANDLookupKey :=
  (a +++ b).toFin

/-- A one-hot row at `idx`. -/
def oneHot {ι : Type} {F : Type u} [DecidableEq ι] [Zero F] [One F]
    (idx : ι) : ι → F :=
  fun k => if k = idx then 1 else 0

/--
The operands observed by the AND tracer at row `i`.

This is part of the tracer, not a second definition of instruction semantics.
It performs the source reads used to fill the lookup-address row.
-/
def traceANDOperands {T : Nat}
    (trace : ExecutionTrace T) (i : Fin T) : Option (BitVec Xlen × BitVec Xlen) :=
  match trace.instr i with
  | .AND _ rs1 rs2 =>
      match (JoltISA.readSrc rs1).run (trace.preState i) with
      | .ok rs1Val afterRs1 =>
          match (JoltISA.readSrc rs2).run afterRs1 with
          | .ok rs2Val _ => some (rs1Val, rs2Val)
          | .error _ _ => none
      | .error _ _ => none
  | _ => none

/--
Stage 1: the AND part of the tracer.

For an AND row it sets the flag, reads the two source values, encodes their
bitwise AND, and places a one at the table row selected by those source values.
For a non-AND row the flag and lookup-address row are zero. This is only the
partial tracer for the data needed by the current constraint.
-/
def traceToJoltData {T : Nat} {F : Type u} [Zero F] [One F]
    (encode : BitVec Xlen → F)
    (trace : ExecutionTrace T) : JoltData T F where
  trace := trace.instr
  AND_FLAG i := if isAND (trace.instr i) = true then 1 else 0
  RD_val i :=
    match traceANDOperands trace i with
    | some (rs1Val, rs2Val) => encode (rs1Val &&& rs2Val)
    | none => 0
  ra i :=
    match traceANDOperands trace i with
    | some (rs1Val, rs2Val) => oneHot (andLookupKey rs1Val rs2Val)
    | none => fun _ => 0

/-- The honest tracer's AND flag says exactly that its instruction is AND. -/
theorem traceToJoltData_AND_FLAG_iff
    {T : Nat} {F : Type u} [Field F]
    (encode : BitVec Xlen → F)
    (trace : ExecutionTrace T)
    (i : Fin T) :
    (traceToJoltData encode trace).ClaimsAND i ↔
      isAND ((traceToJoltData encode trace).trace i) = true := by
  sorry

/-! ## The fixed AND lookup table and its values -/

/-- The 128-bit bitstring represented by a lookup-table index. -/
def ANDLookupKey.bits (key : ANDLookupKey) : BitVec 128 :=
  BitVec.ofFin key

/-- The left 64-bit operand contained in a 128-bit lookup key. -/
def ANDLookupKey.left (key : ANDLookupKey) : BitVec Xlen :=
  Sail.BitVec.extractLsb key.bits 127 64

/-- The right 64-bit operand contained in a 128-bit lookup key. -/
def ANDLookupKey.right (key : ANDLookupKey) : BitVec Xlen :=
  Sail.BitVec.extractLsb key.bits 63 0

/--
The concrete value-level AND table:
`T_AND_values[a || b] = a &&& b`.
-/
def ANDTableValues (key : ANDLookupKey) : BitVec Xlen :=
  key.left &&& key.right

/-- The value-level table encoded into the constraint field. -/
def encodedANDTable {F : Type u}
    (encode : BitVec Xlen → F) : ANDTable F :=
  fun key => encode (ANDTableValues key)

/-- Concatenating operands and looking them up returns their bitwise AND. -/
theorem ANDTableValues_andLookupKey (a b : BitVec Xlen) :
    ANDTableValues (andLookupKey a b) = a &&& b := by
  sorry

/-! ## Main theorem: necessity -/

/--
Correct execution of the AND rows implies that the data produced by the AND
tracer satisfies the specified AND constraint.

This is the necessary direction only.
-/
theorem ANDConstraint_isNecessary
    {T : Nat} {F : Type u} [Field F]
    (trace : ExecutionTrace T)
    (hExecution : trace.Executes)
    (encode : BitVec Xlen → F) :
    ANDConstraint
      (traceToJoltData encode trace)
      (encodedANDTable encode) := by
  sorry

end JoltConstraints
