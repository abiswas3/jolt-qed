import JoltConstraints.basic

/-!
# AND constraint sketch

This is a first sketch of how a lookup constraint should connect back to
`JoltISA.execInstr`.  The theorem is intentionally local to one flagged row:
`AND_FLAG[i]` identifies an AND instruction, the source-linking assumptions say
which values JoltISA reads, and the lookup constraint says the row's `RDVal` is
the table-selected value.  The conclusion states that JoltISA's AND semantics
reaches a write of that `RDVal` to the decoded destination.
-/

namespace JoltConstraints

open scoped BigOperators

/-- Number of rows in the AND lookup table. -/
abbrev AND_TableSize : Nat :=
  2 ^ (2 * Xlen)

/-- The algebraic AND lookup table used by the actual polynomial constraint. -/
structure AND_LookupTable (F : Type) where
  value : Column AND_TableSize F

/-- A pair of `Xlen` values is encoded as one `2 * Xlen` lookup-table row key. -/
abbrev AND_LookupKey : Type :=
  BitVec (2 * Xlen)
/-- The lookup-table row key for operands `a` and `b`. -/
def andLookupKey (a b : BitVec Xlen) : AND_LookupKey :=
  a +++ b

/-- The finite table row corresponding to key `a || b`. -/
def andLookupRow (a b : BitVec Xlen) : Fin AND_TableSize :=
  (andLookupKey a b).toFin

/-- An algebraic lookup-address row over the AND table. -/
abbrev LookupAddressRow (F : Type) : Type :=
  Column AND_TableSize F

/-- The algebraic `T x K` lookup-address matrix, with `K = 2^(2 * Xlen)`. -/
abbrev RA_matrix (T : Nat) (F : Type) : Type :=
  Column T (LookupAddressRow F)

/-- Names for the trace-length witness column families in this sketch. -/
inductive JoltWitness where
  | andFlag
  | rs1Val
  | rs2Val
  | rdVal
  | rdValEncoded
  | lookupAddressMatrix
  deriving Repr, DecidableEq

/-- The Lean type carried by each AND witness column family. -/
def JoltWitness.columnType (T : Nat) (F : Type) : JoltWitness -> Type
  | .andFlag => FlagColumn T
  | .rs1Val => Column T (BitVec Xlen)
  | .rs2Val => Column T (BitVec Xlen)
  | .rdVal => Column T (BitVec Xlen)
  | .rdValEncoded => Column T F
  | .lookupAddressMatrix => RA_matrix T F

/-- The concrete AND witness columns currently modeled in this sketch. -/
structure AND_Witness (T : Nat) (F : Type) where
  AND_FLAG : JoltWitness.columnType T F .andFlag
  rs1Val : JoltWitness.columnType T F .rs1Val
  rs2Val : JoltWitness.columnType T F .rs2Val
  RDVal : JoltWitness.columnType T F .rdVal
  RDValEncoded : JoltWitness.columnType T F .rdValEncoded
  RA_matrix : JoltWitness.columnType T F .lookupAddressMatrix

/-- The predicate "this instruction is some `JoltISA.Instr.AND`". -/
def IsANDInstr (instr : JoltISA.Instr) : Prop :=
  exists (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    instr = JoltISA.Instr.AND rd rs1 rs2

/-- Soundness direction: an active flag determines that the row is AND. -/
def AND_FlagSound {T : Nat} {F : Type} (w : AND_Witness T F) (trace : CpuTrace T) : Prop :=
  forall i : Fin T, w.AND_FLAG i = true -> IsANDInstr (trace.instr i)

/-- Completeness direction: every AND row has the flag set. -/
def AND_FlagComplete {T : Nat} {F : Type} (w : AND_Witness T F) (trace : CpuTrace T) : Prop :=
  forall i : Fin T, IsANDInstr (trace.instr i) -> w.AND_FLAG i = true

/--
Correctness of `AND_FLAG`: both directions of the tracer/flag relationship.
-/
def AND_FlagCorrect {T : Nat} {F : Type} (w : AND_Witness T F) (trace : CpuTrace T) : Prop :=
  AND_FlagSound w trace ∧ AND_FlagComplete w trace

/-- Actual algebraic dot product: `sum_k ra[k] * T_AND[k]`. -/
noncomputable def AND_TableDotAlgebraic
    {F : Type} [Semiring F]
    (table : AND_LookupTable F) (lookupAddress : LookupAddressRow F) : F :=
  Finset.univ.sum (fun k : Fin AND_TableSize =>
    lookupAddress k * table.value k)

/-- Algebraic one-hot row, with its unique `1` at `row` and zero elsewhere. -/
def OneHotAtAlgebraic {K : Nat} {F : Type} [Semiring F]
    (lookupAddress : Column K F) (row : Fin K) : Prop :=
  lookupAddress row = 1 ∧
    forall k : Fin K, k ≠ row -> lookupAddress k = 0

/-- The algebraic AND table has row `a || b` equal to the encoded `a &&& b`. -/
def AND_LookupTableCorrect {F : Type}
    (encode : BitVec Xlen -> F) (table : AND_LookupTable F) : Prop :=
  forall a b : BitVec Xlen, table.value (andLookupRow a b) = encode (a &&& b)

/--
For active AND rows, the `ra` matrix is one-hot at the row corresponding to the
Jolt-read source values `rs1Val || rs2Val`.
-/
def AND_RA_matrixCorrect {T : Nat} {F : Type} [Semiring F]
    (w : AND_Witness T F) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      OneHotAtAlgebraic (w.RA_matrix i) (andLookupRow (w.rs1Val i) (w.rs2Val i))

/--
The polynomial-style dot-product constraint:

`AND_FLAG[i] -> RDVal[i] = sum_k ra[i,k] * T_AND[k]`.
-/
def AND_DotProductConstraint {T : Nat} {F : Type} [Semiring F]
    (w : AND_Witness T F) (table : AND_LookupTable F)
    : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      w.RDValEncoded i = AND_TableDotAlgebraic table (w.RA_matrix i)

/--
The algebraic AND constraints in this sketch.

For now, table correctness is an assumption about the fixed table rather than a
constraint generated by the trace.
-/
structure AND_ConstraintsHold {T : Nat} {F : Type} [Semiring F]
    (encode : BitVec Xlen -> F) (w : AND_Witness T F) (table : AND_LookupTable F) : Prop where
  tableCorrect : AND_LookupTableCorrect encode table
  raMatrix : AND_RA_matrixCorrect w
  dotProduct : AND_DotProductConstraint w table

/-- The algebraic `RDValEncoded` column is the encoding of the BitVec `RDVal` column. -/
def AND_RDValEncodingCorrect {T : Nat} {F : Type}
    (encode : BitVec Xlen -> F) (w : AND_Witness T F) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      w.RDValEncoded i = encode (w.RDVal i)

/-- Assumptions that let an encoded algebraic result be reflected back to BitVecs. -/
structure AND_EncodingLink {T : Nat} {F : Type}
    (encode : BitVec Xlen -> F) (w : AND_Witness T F) : Prop where
  rdVal : AND_RDValEncodingCorrect encode w
  injective : Function.Injective encode

/--
Bridge predicate: the operand witness columns agree with the source values read
by the JoltISA monadic semantics for a decoded AND row.

This is not the AND lookup constraint; it is the trace/witness link needed
before comparing against `JoltISA.execInstr`.
-/
def AND_OperandWitnessesMatchJoltReads {T : Nat} {F : Type}
    (trace : CpuTrace T) (w : AND_Witness T F) : Prop :=
  forall (i : Fin T) (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    trace.instr i = JoltISA.Instr.AND rd rs1 rs2 ->
      exists afterRs1 afterRs2 : SailJoltState,
        (JoltISA.readSrc rs1).run (rowPreState trace i) =
          .ok (w.rs1Val i) afterRs1 ∧
        (JoltISA.readSrc rs2).run afterRs1 =
          .ok (w.rs2Val i) afterRs2

/--
The non-algebraic link between the trace and the AND witness columns.

The flag fields say which rows are decoded as AND.  The operand field says the
operand witness values are the values read by JoltISA for those decoded rows.
-/
structure AND_TraceLink {T : Nat} {F : Type}
    (w : AND_Witness T F) (trace : CpuTrace T) : Prop where
  flagSound : AND_FlagSound w trace
  flagComplete : AND_FlagComplete w trace
  operands : AND_OperandWitnessesMatchJoltReads trace w

/-- The tail of JoltISA's AND instruction after both source reads have happened. -/
def joltWriteDstAndRetire
    (rd : JoltISA.Dst) (value : BitVec Xlen) : JoltMonad ExecutionResult := do
  JoltISA.writeDst rd value
  pure LeanRV64D.Functions.RETIRE_SUCCESS

/-- The decoded registers and intermediate states for one AND row. -/
structure AND_RowContext {T : Nat} {F : Type}
    (w : AND_Witness T F) (trace : CpuTrace T) (i : Fin T) where
  rd : JoltISA.Dst
  rs1 : JoltISA.Src
  rs2 : JoltISA.Src
  afterRs1 : SailJoltState
  afterRs2 : SailJoltState

/-- The trace instruction at this row is the decoded AND instruction. -/
abbrev AND_RowContext.instrMatches
    {T : Nat} {F : Type} {w : AND_Witness T F} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  trace.instr i = JoltISA.Instr.AND row.rd row.rs1 row.rs2

/-- The witnessed source values are the values read by JoltISA. -/
abbrev AND_RowContext.sourceReadsMatch
    {T : Nat} {F : Type} {w : AND_Witness T F} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  (JoltISA.readSrc row.rs1).run (rowPreState trace i) =
    .ok (w.rs1Val i) row.afterRs1 ∧
  (JoltISA.readSrc row.rs2).run row.afterRs1 =
    .ok (w.rs2Val i) row.afterRs2

/-- After the source reads, JoltISA continues by writing the witnessed `RDVal`. -/
abbrev AND_RowContext.execTailMatches
    {T : Nat} {F : Type} {w : AND_Witness T F} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  (JoltISA.execInstr (trace.instr i)).run (rowPreState trace i) =
    (joltWriteDstAndRetire row.rd (w.RDVal i)).run row.afterRs2

/-- Named version of the row-level JoltISA match proved for flagged AND rows. -/
abbrev AND_RowMatchesJolt {T : Nat}
    {F : Type} (w : AND_Witness T F) (trace : CpuTrace T) (i : Fin T) : Prop :=
  exists row : AND_RowContext w trace i,
    row.instrMatches ∧ row.sourceReadsMatch ∧ row.execTailMatches

theorem AND_TableDotAlgebraic_eq_table_of_oneHotAt
    {F : Type} [Semiring F]
    (table : AND_LookupTable F)
    {lookupAddress : LookupAddressRow F} {row : Fin AND_TableSize}
    (h : OneHotAtAlgebraic lookupAddress row) :
    AND_TableDotAlgebraic table lookupAddress = table.value row := by
  classical
  unfold AND_TableDotAlgebraic
  rw [Finset.sum_eq_single row]
  · simp [h.1]
  · intro k _ hk
    have hzero : lookupAddress k = 0 := h.2 k hk
    simp [hzero]
  · intro hnotmem
    simp at hnotmem

/-- The algebraic lookup constraints imply that `RDValEncoded` selects the table row. -/
theorem AND_RDValEncoded_eq_table_value_of_constraints
    {T : Nat} {F : Type} [Semiring F]
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hRA : AND_RA_matrixCorrect w)
    (hDot : AND_DotProductConstraint w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDValEncoded i =
      table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) := by
  calc
    w.RDValEncoded i = AND_TableDotAlgebraic table (w.RA_matrix i) := hDot i hflag
    _ = table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) :=
      AND_TableDotAlgebraic_eq_table_of_oneHotAt table (hRA i hflag)

/--
Packaged version of the first step: the constraints select the table row named
by the witnessed source values.
-/
theorem AND_constraints_select_table_value
    {T : Nat} {F : Type} [Semiring F]
    {encode : BitVec Xlen -> F}
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hConstraints : AND_ConstraintsHold encode w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDValEncoded i =
      table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) := by
  exact AND_RDValEncoded_eq_table_value_of_constraints
    hConstraints.raMatrix hConstraints.dotProduct hflag

/--
Assuming the fixed AND table is correct, the AND lookup constraint computes the
encoded bitwise AND of the two witnessed source values.
-/
theorem AND_RDValEncoded_eq_encoded_bitwise_and_of_constraints
    {T : Nat} {F : Type} [Semiring F]
    {encode : BitVec Xlen -> F}
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hTable : AND_LookupTableCorrect encode table)
    (hRA : AND_RA_matrixCorrect w)
    (hDot : AND_DotProductConstraint w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDValEncoded i = encode (w.rs1Val i &&& w.rs2Val i) := by
  calc
    w.RDValEncoded i =
        table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) :=
      AND_RDValEncoded_eq_table_value_of_constraints hRA hDot hflag
    _ = encode (w.rs1Val i &&& w.rs2Val i) :=
      hTable (w.rs1Val i) (w.rs2Val i)

/--
Packaged final algebraic payoff for this one Jolt constraint.
-/
theorem AND_constraints_compute_encoded_rdval
    {T : Nat} {F : Type} [Semiring F]
    {encode : BitVec Xlen -> F}
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hConstraints : AND_ConstraintsHold encode w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDValEncoded i = encode (w.rs1Val i &&& w.rs2Val i) := by
  calc
    w.RDValEncoded i =
        table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) :=
      AND_constraints_select_table_value hConstraints hflag
    _ = encode (w.rs1Val i &&& w.rs2Val i) :=
      hConstraints.tableCorrect (w.rs1Val i) (w.rs2Val i)

/--
If the encoded `RDVal` column is linked back to the BitVec `RDVal` column, the
algebraic constraint also recovers the BitVec result needed by `execInstr`.
-/
theorem AND_constraints_compute_rdval
    {T : Nat} {F : Type} [Semiring F]
    {encode : BitVec Xlen -> F}
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hConstraints : AND_ConstraintsHold encode w table)
    (hEncoding : AND_EncodingLink encode w)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDVal i = w.rs1Val i &&& w.rs2Val i := by
  apply hEncoding.injective
  calc
    encode (w.RDVal i) = w.RDValEncoded i := (hEncoding.rdVal i hflag).symm
    _ = encode (w.rs1Val i &&& w.rs2Val i) :=
      AND_constraints_compute_encoded_rdval hConstraints hflag

/--
The row-level sketch theorem.

Starting from `AND_FLAG[i] = true`, the trace link recovers the decoded
`.AND rd rs1 rs2` instruction and connects the operand witness columns to the
values read by JoltISA.  The algebraic constraints compute `RDVal[i]`.  Together
these prove that `JoltISA.execInstr` continues by writing that `RDVal[i]` to the
decoded destination.

This still does not prove that the destination-register *index column* is
correct; that will need a separate destination-linking constraint.
-/
theorem AND_flagged_row_execInstr_matches
    {T : Nat} {F : Type} [Semiring F]
    {encode : BitVec Xlen -> F}
    {w : AND_Witness T F} {trace : CpuTrace T}
    {table : AND_LookupTable F}
    (hConstraints : AND_ConstraintsHold encode w table)
    (hEncoding : AND_EncodingLink encode w)
    (hTrace : AND_TraceLink w trace) :
    forall i : Fin T,
      w.AND_FLAG i = true -> AND_RowMatchesJolt w trace i := by
  intro i hflag
  obtain ⟨rd, rs1, rs2, hinstr⟩ := hTrace.flagSound i hflag
  obtain ⟨afterRs1, afterRs2, hreadRs1, hreadRs2⟩ :=
    hTrace.operands i rd rs1 rs2 hinstr
  have hRDVal :
      w.RDVal i = w.rs1Val i &&& w.rs2Val i := by
    exact AND_constraints_compute_rdval hConstraints hEncoding hflag
  let row : AND_RowContext w trace i :=
    { rd, rs1, rs2, afterRs1, afterRs2 }
  refine ⟨row, hinstr, ⟨hreadRs1, hreadRs2⟩, ?_⟩
  dsimp [AND_RowContext.execTailMatches, row]
  rw [hinstr]
  unfold joltWriteDstAndRetire
  simp only [JoltISA.execInstr, EStateM.run, bind, EStateM.bind]
  change JoltISA.readSrc rs1 (rowPreState trace i) =
    .ok (w.rs1Val i) afterRs1 at hreadRs1
  change JoltISA.readSrc rs2 afterRs1 =
    .ok (w.rs2Val i) afterRs2 at hreadRs2
  rw [hreadRs1]
  simp only
  rw [hreadRs2]
  simp only
  rw [← hRDVal]

end JoltConstraints
