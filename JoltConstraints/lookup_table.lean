import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Fin
import JoltConstraints.witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The AND table at a Boolean address:

  And(address) = ∑_{i=0}^{63} 2ⁱ · address[2i+1] · address[2i].

Bits are numbered from the least significant end. The left operand occupies
odd positions and the right operand occupies even positions. A result bit is
set exactly when both corresponding operand bits are set.
Rust: crates/jolt-lookup-tables/src/tables/and.rs. -/
noncomputable def andTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) && address.val.testBit (2 * i.val) then
      (2 : F) ^ i.val
    else 0

/-- `Table_q(x)` from constraint (39) in `constraints.md`: the fixed table's
field value at the 128-bit Boolean address `x`. Only AND is implemented so far. -/
noncomputable def lookupTableEntry {F : Type} [Field F]
    (table : LookupTableKind) (address : Fin (2 ^ 128)) : F :=
  match table with
  | .And => andTableEntry address
  | _ => by sorry

end JoltConstraints
