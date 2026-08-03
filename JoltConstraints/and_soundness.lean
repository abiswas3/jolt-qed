import JoltConstraints.and_tracing

/-!
# AND constraint soundness sketch

This file combines the two separate layers:

* `AND_JoltConstraint`: the actual polynomial constraint;
* `AND_TracingConstraints`: facts produced by reading the trace into witness
  columns.
-/

namespace JoltConstraints

/-! ## Fixed Table Meaning -/

/--
Static table specification:
`T_AND[a || b] = encode (a &&& b)`.

This is neither the gated Jolt constraint nor a trace constraint. It is the
meaning of the fixed lookup table.
-/
def AND_TableSpec {F : Type}
    (encode : BitVec Xlen -> F) (table : AND_LookupTable F) : Prop :=
  forall a b : BitVec Xlen,
    table.value (andLookupRow a b) = encode (a &&& b)

/-! ## Combining The Layers -/

theorem AND_TableDot_eq_table_value_of_oneHot
    {F : Type} [Ring F]
    (table : AND_LookupTable F)
    {addressRow : AND_LookupAddressRow F} {idx : Fin AND_TableSize}
    (hOneHot : ColumnOneHotAtIdx addressRow idx) :
    AND_TableDot table addressRow = table.value idx := by
  classical
  unfold AND_TableDot
  rw [Finset.sum_eq_single idx]
  · simp [hOneHot.1]
  · intro k _ hk
    have hzero : addressRow k = 0 := hOneHot.2 k hk
    simp [hzero]
  · intro hnotmem
    simp at hnotmem

/--
The transitive payoff for one active AND row.

Inputs are deliberately separated:

* `hJolt`: the actual Jolt polynomial constraint;
* `hTracing`: the trace-to-witness constraints;
* `hTable`: the fixed AND table specification;
* `hEncode`: the Lean-side fact that field encoding reflects BitVec equality.
-/
theorem AND_active_row_rdVal_correct
    {T : Nat} {F : Type} [Ring F]
    {encode : BitVec Xlen -> F}
    {trace : CpuTrace T} {tw : AND_TraceWitness T F}
    {table : AND_LookupTable F}
    (hJolt : AND_JoltConstraintsHold tw.jolt table)
    (hTracing : AND_TracingConstraints encode trace tw)
    (hTable : AND_TableSpec encode table)
    (hEncode : Function.Injective encode)
    {i : Fin T} (hFlag : tw.jolt.AND_FLAG i = 1) :
    tw.RDVal i = tw.rs1Val i &&& tw.rs2Val i := by
  apply hEncode
  calc
    encode (tw.RDVal i) = tw.jolt.RDVal i := (hTracing.rdValEncoded i hFlag).symm
    _ = AND_TableDot table (tw.jolt.RA_matrix i) :=
      hJolt.eq_of_flag_one hFlag
    _ = table.value (andLookupRow (tw.rs1Val i) (tw.rs2Val i)) :=
      AND_TableDot_eq_table_value_of_oneHot table (hTracing.lookupAddress i hFlag)
    _ = encode (tw.rs1Val i &&& tw.rs2Val i) :=
      hTable (tw.rs1Val i) (tw.rs2Val i)

end JoltConstraints
