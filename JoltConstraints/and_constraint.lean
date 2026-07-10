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

/-- A pair of `Xlen` values is encoded as one `2 * Xlen` lookup-table row key. -/
abbrev AND_LookupKey : Type :=
  BitVec (2 * Xlen)

/--
The fixed AND lookup table.

Conceptually this is a vector of length `2^(2 * Xlen)`; row `a || b` stores
`a &&& b`.
-/
structure AND_LookupTable where
  value : Column (2 ^ (2 * Xlen)) (BitVec Xlen)

/-- The lookup-table row key for operands `a` and `b`. -/
def andLookupKey (a b : BitVec Xlen) : AND_LookupKey :=
  a +++ b

/-- The finite table row corresponding to key `a || b`. -/
def andLookupRow (a b : BitVec Xlen) : Fin (2 ^ (2 * Xlen)) :=
  (andLookupKey a b).toFin

/-- A one-hot row over the AND table. -/
abbrev AND_SelectorRow : Type :=
  Column (2 ^ (2 * Xlen)) Bool

/-- The `T x K` one-hot matrix, with `K = 2^(2 * Xlen)`. -/
abbrev AND_SelectorMatrix (T : Nat) : Type :=
  Column T AND_SelectorRow

/-- Names for the trace-length AND witness column families in this sketch. -/
inductive AND_WitnessColumn where
  | andFlag
  | rs1Val
  | rs2Val
  | rdVal
  | selector
  deriving Repr, DecidableEq

/-- The Lean type carried by each AND witness column family. -/
def AND_WitnessColumn.columnType (T : Nat) : AND_WitnessColumn -> Type
  | .andFlag => FlagColumn T
  | .rs1Val => Column T (BitVec Xlen)
  | .rs2Val => Column T (BitVec Xlen)
  | .rdVal => Column T (BitVec Xlen)
  | .selector => AND_SelectorMatrix T

/-- The concrete AND witness columns currently modeled in this sketch. -/
structure AND_Witness (T : Nat) where
  AND_FLAG : AND_WitnessColumn.columnType T .andFlag
  rs1Val : AND_WitnessColumn.columnType T .rs1Val
  rs2Val : AND_WitnessColumn.columnType T .rs2Val
  RDVal : AND_WitnessColumn.columnType T .rdVal
  selector : AND_WitnessColumn.columnType T .selector

/-- The predicate "this instruction is some `JoltISA.Instr.AND`". -/
def IsANDInstr (instr : JoltISA.Instr) : Prop :=
  exists (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    instr = JoltISA.Instr.AND rd rs1 rs2

/-- Soundness direction: an active flag determines that the row is AND. -/
def AND_FlagSound {T : Nat} (w : AND_Witness T) (trace : CpuTrace T) : Prop :=
  forall i : Fin T, w.AND_FLAG i = true -> IsANDInstr (trace.instr i)

/-- Completeness direction: every AND row has the flag set. -/
def AND_FlagComplete {T : Nat} (w : AND_Witness T) (trace : CpuTrace T) : Prop :=
  forall i : Fin T, IsANDInstr (trace.instr i) -> w.AND_FLAG i = true

/--
Correctness of `AND_FLAG`: both directions of the tracer/flag relationship.
-/
def AND_FlagCorrect {T : Nat} (w : AND_Witness T) (trace : CpuTrace T) : Prop :=
  AND_FlagSound w trace ∧ AND_FlagComplete w trace

/-- Interpret a Boolean selector as either the selected word or zero. -/
def selectWord (selected : Bool) (value : BitVec Xlen) : BitVec Xlen :=
  if selected then value else 0

/-- Dot product of one selector row with the fixed AND table. -/
noncomputable def AND_TableDot
    (table : AND_LookupTable) (selector : AND_SelectorRow) : BitVec Xlen :=
  Finset.univ.sum (fun k : Fin (2 ^ (2 * Xlen)) =>
    selectWord (selector k) (table.value k))

/-- `selector` is one-hot, with its unique `1` at `row`. -/
def OneHotAt {K : Nat} (selector : Column K Bool) (row : Fin K) : Prop :=
  selector row = true ∧
    forall k : Fin K, selector k = true -> k = row

/-- The fixed AND table has row `a || b` equal to `a &&& b`. -/
def AND_LookupTableCorrect (table : AND_LookupTable) : Prop :=
  forall a b : BitVec Xlen, table.value (andLookupRow a b) = (a &&& b)

/--
For active AND rows, the `ra` matrix is one-hot at the row corresponding to the
Jolt-read source values `rs1Val || rs2Val`.
-/
def AND_SelectorCorrect {T : Nat}
    (w : AND_Witness T) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      OneHotAt (w.selector i) (andLookupRow (w.rs1Val i) (w.rs2Val i))

/--
The polynomial-style dot-product constraint:

`AND_FLAG[i] -> RDVal[i] = sum_k ra[i,k] * T_AND[k]`.
-/
def AND_DotProductConstraint {T : Nat}
    (w : AND_Witness T) (table : AND_LookupTable)
    : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      w.RDVal i = AND_TableDot table (w.selector i)

/--
The operand witness is linked to JoltISA's monadic source reads.

This is currently an assumption/predicate, not a proved constraint: it records
that the lookup inputs for an AND row are exactly what `readSrc rs1` and
`readSrc rs2` produce from the row pre-state.
-/
def AND_SourceReadsMatchJolt {T : Nat}
    (trace : CpuTrace T) (w : AND_Witness T) : Prop :=
  forall (i : Fin T) (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    trace.instr i = JoltISA.Instr.AND rd rs1 rs2 ->
      exists afterRs1 afterRs2 : SailJoltState,
        (JoltISA.readSrc rs1).run (rowPreState trace i) =
          .ok (w.rs1Val i) afterRs1 ∧
        (JoltISA.readSrc rs2).run afterRs1 =
          .ok (w.rs2Val i) afterRs2

/-- The tail of JoltISA's AND instruction after both source reads have happened. -/
def joltWriteDstAndRetire
    (rd : JoltISA.Dst) (value : BitVec Xlen) : JoltMonad ExecutionResult := do
  JoltISA.writeDst rd value
  pure LeanRV64D.Functions.RETIRE_SUCCESS

/-- The decoded registers and intermediate states for one AND row. -/
structure AND_RowContext {T : Nat}
    (w : AND_Witness T) (trace : CpuTrace T) (i : Fin T) where
  rd : JoltISA.Dst
  rs1 : JoltISA.Src
  rs2 : JoltISA.Src
  afterRs1 : SailJoltState
  afterRs2 : SailJoltState

/-- The trace instruction at this row is the decoded AND instruction. -/
abbrev AND_RowContext.instrMatches
    {T : Nat} {w : AND_Witness T} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  trace.instr i = JoltISA.Instr.AND row.rd row.rs1 row.rs2

/-- The witnessed source values are the values read by JoltISA. -/
abbrev AND_RowContext.sourceReadsMatch
    {T : Nat} {w : AND_Witness T} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  (JoltISA.readSrc row.rs1).run (rowPreState trace i) =
    .ok (w.rs1Val i) row.afterRs1 ∧
  (JoltISA.readSrc row.rs2).run row.afterRs1 =
    .ok (w.rs2Val i) row.afterRs2

/-- After the source reads, JoltISA continues by writing the witnessed `RDVal`. -/
abbrev AND_RowContext.execTailMatches
    {T : Nat} {w : AND_Witness T} {trace : CpuTrace T} {i : Fin T}
    (row : AND_RowContext w trace i) : Prop :=
  (JoltISA.execInstr (trace.instr i)).run (rowPreState trace i) =
    (joltWriteDstAndRetire row.rd (w.RDVal i)).run row.afterRs2

/-- Named version of the row-level JoltISA match proved for flagged AND rows. -/
abbrev AND_RowMatchesJolt {T : Nat}
    (w : AND_Witness T) (trace : CpuTrace T) (i : Fin T) : Prop :=
  exists row : AND_RowContext w trace i,
    row.instrMatches ∧ row.sourceReadsMatch ∧ row.execTailMatches

theorem AND_TableDot_eq_table_of_oneHotAt
    (table : AND_LookupTable)
    {selector : AND_SelectorRow} {row : Fin (2 ^ (2 * Xlen))}
    (h : OneHotAt selector row) :
    AND_TableDot table selector = table.value row := by
  classical
  unfold AND_TableDot
  rw [Finset.sum_eq_single row]
  · simp [selectWord, h.1]
  · intro k _ hk
    have hnot : selector k ≠ true := by
      intro hktrue
      exact hk (h.2 k hktrue)
    have hfalse : selector k = false := by
      cases hsel : selector k <;> simp_all
    simp [selectWord, hfalse]
  · intro hnotmem
    simp at hnotmem

/-- The lookup constraints imply that `RDVal` is the value selected by the table. -/
theorem AND_RDVal_eq_table_value_of_constraints
    {T : Nat}
    {w : AND_Witness T} {table : AND_LookupTable}
    (hSelector : AND_SelectorCorrect w)
    (hDot : AND_DotProductConstraint w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDVal i =
      table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) := by
  calc
    w.RDVal i = AND_TableDot table (w.selector i) := hDot i hflag
    _ = table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) :=
      AND_TableDot_eq_table_of_oneHotAt table (hSelector i hflag)

/--
Assuming the fixed AND table is correct, the AND lookup constraint computes the
actual bitwise AND of the two witnessed source values.
-/
theorem AND_RDVal_eq_bitwise_and_of_constraints
    {T : Nat}
    {w : AND_Witness T} {table : AND_LookupTable}
    (hTable : AND_LookupTableCorrect table)
    (hSelector : AND_SelectorCorrect w)
    (hDot : AND_DotProductConstraint w table)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    w.RDVal i = w.rs1Val i &&& w.rs2Val i := by
  calc
    w.RDVal i =
        table.value (andLookupRow (w.rs1Val i) (w.rs2Val i)) :=
      AND_RDVal_eq_table_value_of_constraints hSelector hDot hflag
    _ = w.rs1Val i &&& w.rs2Val i :=
      hTable (w.rs1Val i) (w.rs2Val i)

/--
The current AND witness-correctness package.

`flagSound` and `flagComplete` are the two directions of the tracer/flag
relationship.  The remaining fields state that the other witness columns line
up with Jolt reads and the AND lookup constraint.
-/
structure AND_WitnessCorrect {T : Nat}
    (w : AND_Witness T) (trace : CpuTrace T) (table : AND_LookupTable) : Prop where
  flagSound : AND_FlagSound w trace
  flagComplete : AND_FlagComplete w trace
  sourceReads : AND_SourceReadsMatchJolt trace w
  tableCorrect : AND_LookupTableCorrect table
  selector : AND_SelectorCorrect w
  dotProduct : AND_DotProductConstraint w table

/--
The row-level sketch theorem.

Starting only from `AND_FLAG[i] = true`, the flag soundness predicate recovers
the decoded `.AND rd rs1 rs2` instruction.  The source-read linking predicate
connects the lookup operands to JoltISA's monadic reads.  The lookup/table/dot
constraints then prove that, after those Jolt reads, `execInstr` continues by
writing `RDVal[i]` to the decoded destination.

This still does not prove that the destination-register *index column* is
correct; that will need a separate destination-linking constraint.
-/
theorem AND_flagged_row_matches_jolt_write
    {T : Nat}
    {w : AND_Witness T} {trace : CpuTrace T}
    {table : AND_LookupTable}
    (hCorrect : AND_WitnessCorrect w trace table) :
    forall i : Fin T,
      w.AND_FLAG i = true -> AND_RowMatchesJolt w trace i := by
  intro i hflag
  obtain ⟨rd, rs1, rs2, hinstr⟩ := hCorrect.flagSound i hflag
  obtain ⟨afterRs1, afterRs2, hreadRs1, hreadRs2⟩ :=
    hCorrect.sourceReads i rd rs1 rs2 hinstr
  have hRDVal :
      w.RDVal i = w.rs1Val i &&& w.rs2Val i := by
    exact AND_RDVal_eq_bitwise_and_of_constraints
      hCorrect.tableCorrect hCorrect.selector hCorrect.dotProduct hflag
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
