import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness

set_option autoImplicit false

namespace JoltConstraints

/-- `Table_q(x)` from constraint (39) in `constraints.md`: the fixed table's
field value at the 128-bit Boolean address `x`. -/
noncomputable def lookupTableEntry {F : Type} [Field F]
    (table : LookupTableKind) (address : Fin (2 ^ 128)) : F := by
  sorry

end JoltConstraints
