import JoltConstraints.basic

/-!
# Jolt witness

This file defines only the type of a Jolt witness. It does not define a Jolt
program, an execution trace, witness generation, or any constraints.

The current development models the slice of the Jolt witness needed for the
AND instruction. A witness contains separate families of committed and virtual
polynomial evaluations. Every evaluation array is built from `Column`.
-/

namespace JoltConstraints

universe u

/-! ## Column domains -/

/-- Number of bits in Jolt's register address. -/
abbrev RegisterAddressBits : Nat := 7

/-- Number of entries in Jolt's register address domain. -/
abbrev RegisterAddressCount : Nat := 2 ^ RegisterAddressBits

/-- One index in Jolt's 128-element register address domain. -/
abbrev RegisterAddress : Type := Fin RegisterAddressCount

/-- Number of bits in one logical RV64 instruction-lookup address. -/
abbrev InstructionLookupAddressBits : Nat := 2 * Xlen

/-- Number of entries in the logical instruction-lookup address domain. -/
abbrev InstructionLookupAddressCount : Nat :=
  2 ^ InstructionLookupAddressBits

/-- One logical 128-bit instruction-lookup address. -/
abbrev InstructionLookupAddress : Type := Fin InstructionLookupAddressCount

/-- A row of 128 cycle-columns, one column for each register address. -/
abbrev RegisterColumns (T : Nat) (F : Type u) : Type u :=
  Column RegisterAddressCount (Column T F)

/-- A row of cycle-columns indexed by the full logical lookup address. -/
abbrev InstructionLookupColumns (T : Nat) (F : Type u) : Type u :=
  Column InstructionLookupAddressCount (Column T F)

/-! ## Polynomial identifiers -/

/-- Fixed lookup tables currently represented in the witness vocabulary. -/
inductive JoltLookupTable where
  | AND
  deriving DecidableEq, Repr

/-- Circuit flags currently needed by the AND development. -/
inductive JoltCircuitFlag where
  | addOperands
  | subtractOperands
  | multiplyOperands
  | advice
  | writeLookupOutputToRD
  deriving DecidableEq, Repr

/-- Instruction-routing flags currently needed by the AND development. -/
inductive JoltInstructionFlag where
  | leftOperandIsRs1Value
  | rightOperandIsRs2Value
  | rightOperandIsImm
  deriving DecidableEq, Repr

/--
Committed polynomial identifiers currently modelled.

`instructionRa` is temporarily the full logical read-address family. It
stands in for Rust's physical chunked representation; it is not a claim that
Rust commits one unchunked polynomial.
-/
inductive JoltCommittedPolynomial where
  | rdInc
  -- WARNING: In the real code base this is chunked.
  -- so this will eventually have a chunking parameter d=2 or something like that
  | instructionRa
  deriving DecidableEq, Repr

/-- Virtual polynomial identifiers currently modelled. -/
inductive JoltVirtualPolynomial where
  | leftLookupOperand
  | rightLookupOperand
  | leftInstructionInput
  | rightInstructionInput
  | rs1Value
  | rs2Value
  | rdWriteValue
  | lookupOutput
  | instructionRafFlag
  | rs1Ra
  | rs2Ra
  | rdWa
  | opFlag (flag : JoltCircuitFlag)
  | instructionFlag (flag : JoltInstructionFlag)
  | lookupTableFlag (table : JoltLookupTable)
  deriving DecidableEq, Repr

/-! ## Evaluation shapes -/

/-- The type of the evaluations belonging to a committed polynomial. -/
def JoltCommittedPolynomial.EvaluationsType
    (polynomial : JoltCommittedPolynomial)
    (T : Nat) (F : Type u) : Type u :=
  match polynomial with
  | .rdInc => Column T F
  | .instructionRa => InstructionLookupColumns T F

/-- The evaluation type belonging to a virtual polynomial. -/
def JoltVirtualPolynomial.EvaluationsType
    (polynomial : JoltVirtualPolynomial)
    (T : Nat) (F : Type u) : Type u :=
  match polynomial with
  | .rs1Ra
  | .rs2Ra
  | .rdWa => RegisterColumns T F
  | _ => Column T F

/-! ## Witness -/

/--
The currently modelled Jolt witness.

The two fields preserve Jolt's protocol-level distinction:

* `committed` contains the evaluation arrays that are committed by the prover;
* `virtual` contains evaluation arrays of virtual polynomials.

The type records the arrays available to the constraint layer; it does not say
that virtual arrays are independent witness choices. Their defining relations
will be represented separately as constraints.
-/
structure JoltWitness (T : Nat) (F : Type u) where
  committed : (polynomial : JoltCommittedPolynomial) →
    polynomial.EvaluationsType T F
  virtual : (polynomial : JoltVirtualPolynomial) →
    polynomial.EvaluationsType T F

/-! ## Typed accessors -/

/-- Committed destination-register increment (`RdInc`). -/
def JoltWitness.rdInc {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.committed .rdInc

/-- Logical instruction read-address family before Rust's chunking. -/
def JoltWitness.instructionRa {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : InstructionLookupColumns T F :=
  witness.committed .instructionRa

/-- Left operand supplied to the instruction lookup. -/
def JoltWitness.leftLookupOperand {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .leftLookupOperand

/-- Right operand supplied to the instruction lookup. -/
def JoltWitness.rightLookupOperand {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .rightLookupOperand

/-- Left input selected by the instruction flags. -/
def JoltWitness.leftInstructionInput {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .leftInstructionInput

/-- Right input selected by the instruction flags. -/
def JoltWitness.rightInstructionInput {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .rightInstructionInput

/-- Value read from `rs1`. -/
def JoltWitness.rs1Value {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .rs1Value

/-- Value read from `rs2`. -/
def JoltWitness.rs2Value {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .rs2Value

/-- Value claimed to be written to `rd`. -/
def JoltWitness.rdWriteValue {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .rdWriteValue

/-- Output of the selected instruction lookup table. -/
def JoltWitness.lookupOutput {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .lookupOutput

/-- Whether the instruction lookup uses the RAF path. -/
def JoltWitness.instructionRafFlag {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.virtual .instructionRafFlag

/-- One-hot register read address for `rs1`. -/
def JoltWitness.rs1Ra {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : RegisterColumns T F :=
  witness.virtual .rs1Ra

/-- One-hot register read address for `rs2`. -/
def JoltWitness.rs2Ra {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : RegisterColumns T F :=
  witness.virtual .rs2Ra

/-- One-hot register write address for `rd`. -/
def JoltWitness.rdWa {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : RegisterColumns T F :=
  witness.virtual .rdWa

/-- A virtual circuit-flag column. -/
def JoltWitness.opFlag {T : Nat} {F : Type u}
    (witness : JoltWitness T F) (flag : JoltCircuitFlag) : Column T F :=
  witness.virtual (.opFlag flag)

/-- A virtual instruction-routing flag column. -/
def JoltWitness.instructionFlag {T : Nat} {F : Type u}
    (witness : JoltWitness T F) (flag : JoltInstructionFlag) : Column T F :=
  witness.virtual (.instructionFlag flag)

/-- A virtual fixed-table selector column. -/
def JoltWitness.lookupTableFlag {T : Nat} {F : Type u}
    (witness : JoltWitness T F) (table : JoltLookupTable) : Column T F :=
  witness.virtual (.lookupTableFlag table)

/-- `OpFlags(WriteLookupOutputToRD)`. -/
def JoltWitness.writeLookupOutputToRD {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.opFlag .writeLookupOutputToRD

/-! ## Specification-facing names -/

/-- Specification name for the AND lookup-table selector. -/
def JoltWitness.AND_FLAG {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.lookupTableFlag .AND

/-- Specification name for the destination write-value column. -/
def JoltWitness.RD_val {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : Column T F :=
  witness.rdWriteValue

/-- Specification name for the logical instruction read-address family. -/
def JoltWitness.ra {T : Nat} {F : Type u}
    (witness : JoltWitness T F) : InstructionLookupColumns T F :=
  witness.instructionRa

end JoltConstraints
