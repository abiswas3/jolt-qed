import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage4` classifies the five witness identities tested by Rust's two Stage 4
sumchecks:

* `RegistersReadWriteChecking` gamma-batches the destination write, first
  source read, and second source read identities; and
* `RamValCheck` gamma-batches the running and final RAM-value identities.

The `LtPolynomial` table is represented here by `strictPrefixSum`; it is part
of the single `RamValCheck` sumcheck, not a separate constraint.
-/

def stage4 : JoltConstraint → Bool
  | .rs1ValueEqSelectedRegistersVal
  | .rs2ValueEqSelectedRegistersVal
  | .rdWriteValueEqSelectedRegistersValPlusIncrement
  | .ramValEqInitialValuePlusPriorIncrements
  | .ramValFinalEqInitialValuePlusAllIncrements => true
  | _ => false

end JoltConstraints
