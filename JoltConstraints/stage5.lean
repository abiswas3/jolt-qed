import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage5` classifies the four Stage 5 witness identities in Rust:

* `InstructionReadRaf` gamma-batches lookup output and left/right lookup
  operand evaluation at the address selected by the instruction RA chunks;
  and
* `RegistersValEvaluation` checks that the register-state table is the strict
  prefix accumulation of destination increments.

`RamRaClaimReduction` is a claim reduction, so it is intentionally not a
`JoltConstraint`.
-/

def stage5 : JoltConstraint → Bool
  | .lookupOutputEqInstructionReadRaf
  | .leftLookupOperandEqInstructionReadRaf
  | .rightLookupOperandEqInstructionReadRaf
  | .registersValEqPriorWrites => true
  | _ => false

end JoltConstraints
