import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage2` classifies the seven witness identities tested by Rust's four Stage 2
witness sumchecks:

* `SpartanProductVirtualization` tests the three product identities;
* `RamReadWriteChecking` gamma-batches its two read/write identities;
* `RamRafEvaluation` tests the RAM-address identity; and
* `RamOutputCheck` tests the public-output identity.

The product uni-skip and remainder are two round ranges of the single
`SpartanProductVirtualization` sumcheck, so they are not separate Lean
constraints. Rust's fifth Stage 2 batch member, `InstructionClaimReduction`, is
a claim reduction rather than a witness identity and is therefore not a
`JoltConstraint`.
-/

def stage2 : JoltConstraint → Bool
  | .productEqLeftInputMulRightInput
  | .shouldBranchEqLookupOutputMulBranch
  | .shouldJumpEqJumpMulNotNextIsNoop
  | .ramReadValueEqSelectedRamValue
  | .ramWriteValueEqSelectedRamValuePlusIncrement
  | .ramAddressEqSelectedRamAddress
  | .ramFinalValueEqPublicIo => true
  | _ => false

end JoltConstraints
