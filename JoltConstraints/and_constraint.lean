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

/-- A one-hot row over the AND table. -/
abbrev AND_SelectorRow : Type :=
  Column (2 ^ 128) Bool

/-- The `T x K` one-hot matrix, with `K = 2^128`. -/
abbrev AND_SelectorMatrix (T : Nat) : Type :=
  Column T AND_SelectorRow

/-- Interpret a Boolean selector as either the selected word or zero. -/
def selectWord (selected : Bool) (value : Word) : Word :=
  if selected then value else 0

/-- Dot product of one selector row with the fixed AND table. -/
noncomputable def AND_TableDot
    (table : AND_LookupTable) (selector : AND_SelectorRow) : Word :=
  Finset.univ.sum (fun k : Fin (2 ^ 128) =>
    selectWord (selector k) (table.value k))

/-- `selector` is one-hot, with its unique `1` at `row`. -/
def OneHotAt {K : Nat} (selector : Column K Bool) (row : Fin K) : Prop :=
  selector row = true ∧
    forall k : Fin K, selector k = true -> k = row

/-- The fixed AND table has row `a || b` equal to `a &&& b`. -/
def AND_LookupTableCorrect (table : AND_LookupTable) : Prop :=
  forall a b : Word, table.value (andLookupRow a b) = (a &&& b)

/--
For active AND rows, the `ra` matrix is one-hot at the row corresponding to the
Jolt-read source values `rs1Val || rs2Val`.
-/
def AND_SelectorCorrect {T : Nat}
    (w : Witness T) (lookup : AND_LookupWitness T)
    (ra : AND_SelectorMatrix T) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      OneHotAt (ra i) (andLookupRow (lookup.rs1Val i) (lookup.rs2Val i))

/--
The polynomial-style dot-product constraint:

`AND_FLAG[i] -> RDVal[i] = sum_k ra[i,k] * T_AND[k]`.
-/
def AND_DotProductConstraint {T : Nat}
    (w : Witness T) (table : AND_LookupTable)
    (ra : AND_SelectorMatrix T) (rdValues : RDValueTable T) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i = true ->
      rdValues.RDVal i = AND_TableDot table (ra i)

/--
The operand witness is linked to JoltISA's monadic source reads.

This is currently an assumption/predicate, not a proved constraint: it records
that the lookup inputs for an AND row are exactly what `readSrc rs1` and
`readSrc rs2` produce from the row pre-state.
-/
def AND_SourceReadsMatchJolt {T : Nat}
    (trace : CpuTrace T) (lookup : AND_LookupWitness T) : Prop :=
  forall (i : Fin T) (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src),
    trace.instr i = JoltISA.Instr.AND rd rs1 rs2 ->
      exists afterRs1 afterRs2 : SailJoltState,
        (JoltISA.readSrc rs1).run (rowPreState trace i) =
          .ok (lookup.rs1Val i) afterRs1 ∧
        (JoltISA.readSrc rs2).run afterRs1 =
          .ok (lookup.rs2Val i) afterRs2

/-- The tail of JoltISA's AND instruction after both source reads have happened. -/
def joltWriteDstAndRetire
    (rd : JoltISA.Dst) (value : Word) : JoltMonad ExecutionResult := do
  JoltISA.writeDst rd value
  pure LeanRV64D.Functions.RETIRE_SUCCESS

theorem AND_TableDot_eq_table_of_oneHotAt
    (table : AND_LookupTable)
    {selector : AND_SelectorRow} {row : Fin (2 ^ 128)}
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
    {w : Witness T} {table : AND_LookupTable}
    {lookup : AND_LookupWitness T} {ra : AND_SelectorMatrix T}
    {rdValues : RDValueTable T}
    (hSelector : AND_SelectorCorrect w lookup ra)
    (hDot : AND_DotProductConstraint w table ra rdValues)
    {i : Fin T} (hflag : w.AND_FLAG i = true) :
    rdValues.RDVal i =
      table.value (andLookupRow (lookup.rs1Val i) (lookup.rs2Val i)) := by
  calc
    rdValues.RDVal i = AND_TableDot table (ra i) := hDot i hflag
    _ = table.value (andLookupRow (lookup.rs1Val i) (lookup.rs2Val i)) :=
      AND_TableDot_eq_table_of_oneHotAt table (hSelector i hflag)

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
    {w : Witness T} {trace : CpuTrace T}
    {table : AND_LookupTable} {lookup : AND_LookupWitness T}
    {ra : AND_SelectorMatrix T} {rdValues : RDValueTable T}
    (hFlagSound : AND_FlagSound w trace)
    (hSourceReads : AND_SourceReadsMatchJolt trace lookup)
    (hTable : AND_LookupTableCorrect table)
    (hSelector : AND_SelectorCorrect w lookup ra)
    (hDot : AND_DotProductConstraint w table ra rdValues) :
    forall i : Fin T,
      w.AND_FLAG i = true ->
        exists (rd : JoltISA.Dst) (rs1 rs2 : JoltISA.Src)
          (afterRs1 afterRs2 : SailJoltState),
          trace.instr i = JoltISA.Instr.AND rd rs1 rs2 ∧
          (JoltISA.readSrc rs1).run (rowPreState trace i) =
            .ok (lookup.rs1Val i) afterRs1 ∧
          (JoltISA.readSrc rs2).run afterRs1 =
            .ok (lookup.rs2Val i) afterRs2 ∧
          (JoltISA.execInstr (trace.instr i)).run (rowPreState trace i) =
            (joltWriteDstAndRetire rd (rdValues.RDVal i)).run afterRs2 := by
  intro i hflag
  obtain ⟨rd, rs1, rs2, hinstr⟩ := hFlagSound i hflag
  obtain ⟨afterRs1, afterRs2, hreadRs1, hreadRs2⟩ :=
    hSourceReads i rd rs1 rs2 hinstr
  have hRDVal :
      rdValues.RDVal i = lookup.rs1Val i &&& lookup.rs2Val i := by
    calc
      rdValues.RDVal i =
          table.value (andLookupRow (lookup.rs1Val i) (lookup.rs2Val i)) :=
        AND_RDVal_eq_table_value_of_constraints hSelector hDot hflag
      _ = lookup.rs1Val i &&& lookup.rs2Val i :=
        hTable (lookup.rs1Val i) (lookup.rs2Val i)
  refine ⟨rd, rs1, rs2, afterRs1, afterRs2, hinstr, hreadRs1, hreadRs2, ?_⟩
  rw [hinstr]
  unfold joltWriteDstAndRetire
  simp only [JoltISA.execInstr, EStateM.run, bind, EStateM.bind]
  change JoltISA.readSrc rs1 (rowPreState trace i) =
    .ok (lookup.rs1Val i) afterRs1 at hreadRs1
  change JoltISA.readSrc rs2 afterRs1 =
    .ok (lookup.rs2Val i) afterRs2 at hreadRs2
  rw [hreadRs1]
  simp only
  rw [hreadRs2]
  simp only
  rw [← hRDVal]

end JoltConstraints
