import JoltConstraints.basic

/-!
# Jolt polynomial data

Jolt's witness is organised as named committed and virtual polynomials.  In
this development a polynomial is represented by its evaluations on the
relevant Boolean hypercube.  For a trace polynomial those evaluations are a
`Column T F`; the instruction lookup-address polynomial is the `T × 2^128`
matrix from the specification.

Only the polynomial identifiers needed by the first AND constraint are listed
here.  New identifiers extend these inductive types without changing how
constraints access polynomial data.
-/

namespace JoltConstraints

universe u

/-! ## Instruction lookup domain -/

/-- One 64-bit instruction-lookup operand. -/
abbrev InstructionLookupOperand : Type := Fin (2 ^ Xlen)

/-- A lookup address consists of the two 64-bit instruction operands. -/
abbrev InstructionLookupKey : Type :=
  InstructionLookupOperand × InstructionLookupOperand

/-- One row of the instruction lookup-address matrix. -/
abbrev InstructionLookupVector (F : Type u) : Type u :=
  InstructionLookupKey → F

/-! ## Polynomial identifiers -/

/-- Fixed instruction lookup tables currently known to the constraint layer. -/
inductive JoltLookupTable where
  | AND
  deriving DecidableEq, Repr

/--
Committed (or "real") Jolt polynomials currently used by the model.

`instructionRa` denotes the full `ra(i, k)` instruction lookup-address matrix.
-/
inductive JoltCommittedPolynomial where
  | instructionRa
  deriving DecidableEq, Repr

/-- Virtual Jolt polynomials currently used by the model. -/
inductive JoltVirtualPolynomial where
  | rdWriteValue
  | lookupTableFlag (table : JoltLookupTable)
  deriving DecidableEq, Repr

/-- A name for any currently modelled Jolt witness polynomial. -/
inductive JoltPolynomial where
  | committed (id : JoltCommittedPolynomial)
  | virtual (id : JoltVirtualPolynomial)
  deriving DecidableEq, Repr

/-! Canonical polynomial names.  These expose stable, concise identifiers
without repeating the committed/virtual classification at every use site. -/

/-- The committed instruction lookup-address polynomial. -/
def JoltPolynomial.instructionRa : JoltPolynomial :=
  .committed .instructionRa

/-- The virtual destination-write-value polynomial. -/
def JoltPolynomial.rdWriteValue : JoltPolynomial :=
  .virtual .rdWriteValue

/-- The virtual selector polynomial for the AND lookup table. -/
def JoltPolynomial.andFlag : JoltPolynomial :=
  .virtual (.lookupTableFlag .AND)

/-! ## Evaluation storage -/

/--
The type of the hypercube evaluation array belonging to a polynomial.

Most current polynomials have one evaluation per trace row.  `instructionRa`
has one lookup-address vector per trace row, equivalently a `T × 2^128`
array.
-/
def JoltPolynomial.Evaluations
    (polynomial : JoltPolynomial) (T : Nat) (F : Type u) : Type u :=
  match polynomial with
  | JoltPolynomial.committed .instructionRa =>
      Column T (InstructionLookupVector F)
  | JoltPolynomial.virtual _ => Column T F

/-- All currently modelled Jolt polynomial evaluation arrays. -/
structure JoltPolynomialData (T : Nat) (F : Type u) where
  evals : (polynomial : JoltPolynomial) → polynomial.Evaluations T F

/--
The prover-facing Jolt data.

The instruction trace is semantic metadata.  Field-valued witness data lives
in the named polynomial store.
-/
structure JoltData (T : Nat) (F : Type u) where
  trace : Column T JoltISA.Instr
  polynomials : JoltPolynomialData T F

/-! ## Typed accessors -/

/-- The committed instruction lookup-address matrix `ra(i, k)`. -/
def JoltData.instructionRa {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (InstructionLookupVector F) :=
  data.polynomials.evals JoltPolynomial.instructionRa

/-- The virtual value written to `rd` at each row. -/
def JoltData.rdWriteValue {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rdWriteValue

/-- The virtual selector for a fixed instruction lookup table. -/
def JoltData.lookupTableFlag {T : Nat} {F : Type u}
    (data : JoltData T F) (table : JoltLookupTable) : Column T F :=
  data.polynomials.evals
    (JoltPolynomial.virtual (.lookupTableFlag table))

/-! Specification-facing aliases used by the AND constraint. -/

/-- `AND_FLAG[i] = 1` claims that row `i` uses the AND lookup table. -/
def JoltData.AND_FLAG {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.andFlag

/-- Specification name for the shared `rdWriteValue` virtual polynomial. -/
def JoltData.RD_val {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.rdWriteValue

/-- Specification name for the shared committed instruction `ra` matrix. -/
def JoltData.ra {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (InstructionLookupVector F) :=
  data.instructionRa

end JoltConstraints
