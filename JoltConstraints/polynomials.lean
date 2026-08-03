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
Committed (or "real") Jolt polynomials currently used by the model.

`instructionRa` denotes the full `ra(i, k)` instruction lookup-address matrix.
-/
inductive JoltCommittedPolynomial where
  | rdInc
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

/-! ## Evaluation storage -/

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

/-- All currently modelled Jolt polynomial evaluation arrays. -/
structure JoltPolynomialData (T : Nat) (F : Type u) where
  -- each polynomial has a different return type. 
  evals : (polynomial : JoltPolynomial) → polynomial.EvaluationsType T F

/--
The prover-facing Jolt data.

The instruction trace is semantic metadata.  Field-valued witness data lives
in the named polynomial store.
-/
structure JoltData (T : Nat) (F : Type u) where
  trace : Column T JoltISA.Instr
  polynomials : JoltPolynomialData T F

/-! ## Typed accessors -/

/-- The committed change in the destination register value at each row. -/
def JoltData.rdInc {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rdInc

/-- The committed instruction lookup-address matrix `ra(i, k)`. -/
def JoltData.instructionRa {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (InstructionLookupVector F) :=
  data.polynomials.evals JoltPolynomial.instructionRa

/-- The left operand sent to the instruction lookup. -/
def JoltData.leftLookupOperand {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.leftLookupOperand

/-- The right operand sent to the instruction lookup. -/
def JoltData.rightLookupOperand {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rightLookupOperand

/-- The left input selected from the instruction's decoded inputs. -/
def JoltData.leftInstructionInput {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.leftInstructionInput

/-- The right input selected from the instruction's decoded inputs. -/
def JoltData.rightInstructionInput {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rightInstructionInput

/-- The value read from `rs1` at each row. -/
def JoltData.rs1Value {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rs1Value

/-- The value read from `rs2` at each row. -/
def JoltData.rs2Value {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rs2Value

/-- The virtual value written to `rd` at each row. -/
def JoltData.rdWriteValue {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.rdWriteValue

/-- The one-hot `rs1` register read-address matrix. -/
def JoltData.rs1Ra {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (RegisterAddressVector F) :=
  data.polynomials.evals JoltPolynomial.rs1Ra

/-- The one-hot `rs2` register read-address matrix. -/
def JoltData.rs2Ra {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (RegisterAddressVector F) :=
  data.polynomials.evals JoltPolynomial.rs2Ra

/-- The one-hot destination register write-address matrix. -/
def JoltData.rdWa {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T (RegisterAddressVector F) :=
  data.polynomials.evals JoltPolynomial.rdWa

/-- The output returned by the selected instruction lookup table. -/
def JoltData.lookupOutput {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.lookupOutput

/-- Whether the instruction lookup uses the RAF identity path. -/
def JoltData.instructionRafFlag {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.polynomials.evals JoltPolynomial.instructionRafFlag

/-- A virtual circuit-flag polynomial. -/
def JoltData.opFlag {T : Nat} {F : Type u}
    (data : JoltData T F) (flag : JoltCircuitFlag) : Column T F :=
  data.polynomials.evals (JoltPolynomial.virtual (.opFlag flag))

/-- A virtual instruction-input flag polynomial. -/
def JoltData.instructionFlag {T : Nat} {F : Type u}
    (data : JoltData T F) (flag : JoltInstructionFlag) : Column T F :=
  data.polynomials.evals (JoltPolynomial.virtual (.instructionFlag flag))

/-- The virtual selector for a fixed instruction lookup table. -/
def JoltData.lookupTableFlag {T : Nat} {F : Type u}
    (data : JoltData T F) (table : JoltLookupTable) : Column T F :=
  data.polynomials.evals
    (JoltPolynomial.virtual (.lookupTableFlag table))

/-- The R1CS selector guarding writes of the lookup output to `rd`. -/
def JoltData.writeLookupOutputToRD {T : Nat} {F : Type u}
    (data : JoltData T F) : Column T F :=
  data.opFlag .writeLookupOutputToRD

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
