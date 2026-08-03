import JoltConstraints.basic

/-!
# AND Jolt constraint

This file contains the algebraic Jolt constraint for the AND lookup only.

It does not say how the witness columns were produced from a CPU trace.  Those
are tracing constraints and live in `JoltConstraints.and_tracing`.
-/

namespace JoltConstraints

open scoped BigOperators

/-! ## Witness Columns Used By The Jolt Constraint -/

/-- Number of rows in the AND lookup table: one row for each `rs1 || rs2`. -/
abbrev AND_TableSize : Nat :=
  2 ^ (2 * Xlen)

/-- One lookup-address row over the AND table. -/
abbrev AND_LookupAddressRow (F : Type) : Type :=
  Column AND_TableSize F

/-- The `T x K` lookup-address matrix, with `K = 2^(2 * Xlen)`. -/
abbrev AND_RA_matrix (T : Nat) (F : Type) : Type :=
  Column T (AND_LookupAddressRow F)

/-- The algebraic AND lookup table used by the polynomial constraint. -/
structure AND_LookupTable (F : Type) where
  value : Column AND_TableSize F

/--
The algebraic witness columns that the AND Jolt constraint directly reads.

These are field/ring-valued columns. BitVec source values and trace decoding are
handled by the tracing layer, not by this structure.
-/
structure AND_Witness (T : Nat) (F : Type) where
  AND_FLAG : FlagColumn T F
  RDVal : Column T F
  RA_matrix : AND_RA_matrix T F

/-! ## The Jolt Constraint -/

/-- Actual dot product appearing in the lookup constraint: `sum_k ra[k] * T_AND[k]`. -/
noncomputable def AND_TableDot
    {F : Type} [Ring F]
    (table : AND_LookupTable F) (addressRow : AND_LookupAddressRow F) : F :=
  Finset.univ.sum (fun k : Fin AND_TableSize =>
    addressRow k * table.value k)

/--
The AND Jolt constraint, literally:

`AND_FLAG[i] * (RDVal[i] - sum_k RA_matrix[i,k] * T_AND[k]) = 0`.
-/
def AND_JoltConstraint {T : Nat} {F : Type} [Ring F]
    (w : AND_Witness T F) (table : AND_LookupTable F) : Prop :=
  forall i : Fin T,
    w.AND_FLAG i * (w.RDVal i - AND_TableDot table (w.RA_matrix i)) = 0

/-- Named package for the AND Jolt constraint layer. -/
structure AND_JoltConstraintsHold {T : Nat} {F : Type} [Ring F]
    (w : AND_Witness T F) (table : AND_LookupTable F) : Prop where
  dotProduct : AND_JoltConstraint w table

/--
Immediate consequence of the Jolt constraint on an active row.

This is not a second constraint. It is just algebraic unpacking of
`AND_FLAG[i] * (RDVal[i] - dot) = 0` under `AND_FLAG[i] = 1`.
-/
theorem AND_JoltConstraint.eq_of_flag_one
    {T : Nat} {F : Type} [Ring F]
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hConstraint : AND_JoltConstraint w table)
    {i : Fin T} (hFlag : w.AND_FLAG i = 1) :
    w.RDVal i = AND_TableDot table (w.RA_matrix i) := by
  have h := hConstraint i
  rw [hFlag] at h
  exact sub_eq_zero.mp (by simpa using h)

theorem AND_JoltConstraintsHold.eq_of_flag_one
    {T : Nat} {F : Type} [Ring F]
    {w : AND_Witness T F} {table : AND_LookupTable F}
    (hConstraints : AND_JoltConstraintsHold w table)
    {i : Fin T} (hFlag : w.AND_FLAG i = 1) :
    w.RDVal i = AND_TableDot table (w.RA_matrix i) :=
  hConstraints.dotProduct.eq_of_flag_one hFlag

end JoltConstraints
