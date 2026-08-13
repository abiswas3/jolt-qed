import JoltConstraints.basic

/-!
# Jolt polynomial data

Jolt's witness is organised as named committed and virtual polynomials.  In
this development a polynomial is represented by its evaluations on the
relevant Boolean hypercube.  For a trace polynomial those evaluations are a
`Column T F`; instruction lookup addresses currently use the unchunked logical
`T × 2^128` matrix from the specification. Rust physically represents that
logical address through families of chunked committed and virtual RA
polynomials. Those physical families are not yet represented here.

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

/-! ## Register lookup domain -/

/-- One address in Jolt's 7-bit, 128-entry register space. -/
abbrev RegisterAddress : Type := BitVec 7

/-- One row of a register read- or write-address matrix. -/
abbrev RegisterAddressVector (F : Type u) : Type u :=
  RegisterAddress → F

/-! ## Polynomial identifiers -/

/-- Fixed instruction lookup tables currently known to the constraint layer. -/
inductive JoltLookupTable where
  | AND
  deriving DecidableEq, Repr

/--
Committed (or "real") Jolt polynomials currently used by the model, together
with the temporary logical instruction-RA view described below.

`instructionRa` denotes the full logical `ra(i, k)` instruction lookup-address
matrix. It is not one physical Rust committed polynomial: Rust's
`InstructionRa(usize)` family stores chunks of the same lookup index. Keeping
this distinction explicit prevents the logical view from being mistaken for
the eventual exact physical array model.
-/
inductive JoltCommittedPolynomial where
  | rdInc
  -- WARNING: In the real code base this is chunked.
  | instructionRa
  deriving DecidableEq, Repr

/-- Circuit flags currently needed by the AND-table witness projection. -/
inductive JoltCircuitFlag where
  | writeLookupOutputToRD
  deriving DecidableEq, Repr

/-- Instruction-input flags currently needed by the AND-table projection. -/
inductive JoltInstructionFlag where
  | leftOperandIsRs1Value
  | rightOperandIsRs2Value
  | rightOperandIsImm
  deriving DecidableEq, Repr

/-- Virtual Jolt polynomials currently used by the model. -/
inductive JoltVirtualPolynomial where
  | leftLookupOperand
  | rightLookupOperand
  | leftInstructionInput
  | rightInstructionInput
  | rs1Value
  | rs2Value
  | rdWriteValue
  | rs1Ra
  | rs2Ra
  | rdWa
  | lookupOutput
  | instructionRafFlag
  | opFlag (flag : JoltCircuitFlag)
  | instructionFlag (flag : JoltInstructionFlag)
  | lookupTableFlag (table : JoltLookupTable)
  deriving DecidableEq, Repr

/-- A name for any currently modelled Jolt witness polynomial. -/
inductive JoltPolynomial where
  | committed (id : JoltCommittedPolynomial)
  | virtual (id : JoltVirtualPolynomial)
  deriving DecidableEq, Repr

/-! Canonical polynomial names.  These expose stable, concise identifiers
without repeating the committed/virtual classification at every use site. -/

def JoltPolynomial.rdInc : JoltPolynomial := .committed .rdInc
def JoltPolynomial.instructionRa : JoltPolynomial := .committed .instructionRa
def JoltPolynomial.leftLookupOperand : JoltPolynomial := .virtual .leftLookupOperand
def JoltPolynomial.rightLookupOperand : JoltPolynomial := .virtual .rightLookupOperand
def JoltPolynomial.leftInstructionInput : JoltPolynomial := .virtual .leftInstructionInput
def JoltPolynomial.rightInstructionInput : JoltPolynomial := .virtual .rightInstructionInput
def JoltPolynomial.rs1Value : JoltPolynomial := .virtual .rs1Value
def JoltPolynomial.rs2Value : JoltPolynomial := .virtual .rs2Value
def JoltPolynomial.rdWriteValue : JoltPolynomial := .virtual .rdWriteValue
def JoltPolynomial.rs1Ra : JoltPolynomial := .virtual .rs1Ra
def JoltPolynomial.rs2Ra : JoltPolynomial := .virtual .rs2Ra
def JoltPolynomial.rdWa : JoltPolynomial := .virtual .rdWa
def JoltPolynomial.lookupOutput : JoltPolynomial := .virtual .lookupOutput
def JoltPolynomial.instructionRafFlag : JoltPolynomial := .virtual .instructionRafFlag
def JoltPolynomial.writeLookupOutputToRD : JoltPolynomial :=
  .virtual (.opFlag .writeLookupOutputToRD)
def JoltPolynomial.leftOperandIsRs1Value : JoltPolynomial :=
  .virtual (.instructionFlag .leftOperandIsRs1Value)
def JoltPolynomial.rightOperandIsRs2Value : JoltPolynomial :=
  .virtual (.instructionFlag .rightOperandIsRs2Value)
def JoltPolynomial.rightOperandIsImm : JoltPolynomial :=
  .virtual (.instructionFlag .rightOperandIsImm)
def JoltPolynomial.andFlag : JoltPolynomial := .virtual (.lookupTableFlag .AND)

/-! ## Evaluation shapes -/

/--
The type of the hypercube evaluation array belonging to a polynomial.
-/
def JoltPolynomial.EvaluationsType (polynomial : JoltPolynomial) (T : Nat) (F : Type u) : Type u :=
  match polynomial with
  | JoltPolynomial.committed .instructionRa => Column T (InstructionLookupVector F)
  | JoltPolynomial.virtual .rs1Ra
  | JoltPolynomial.virtual .rs2Ra
  | JoltPolynomial.virtual .rdWa => Column T (RegisterAddressVector F)
  | _ => Column T F

end JoltConstraints
