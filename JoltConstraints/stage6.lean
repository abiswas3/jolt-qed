import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage6` currently classifies the three coefficient-level witness identities
inside Rust's single `Booleanity` sumcheck and the instruction-RA
virtualization identity. Rust gamma-batches the instruction, bytecode, and RAM
committed-RA booleanity families; splitting them here does not introduce three
sumchecks.

The remaining Stage 6 witness relations are added only with their corresponding
honest-witness completeness proofs. Claim reductions and the fixed/public
bytecode read-RAF are intentionally outside this partial classifier for now.
-/

def stage6 : JoltConstraint → Bool
  | .instructionRaBooleanity
  | .bytecodeRaBooleanity
  | .ramRaBooleanity
  | .instructionRaVirtualization
  | .ramRaVirtualization
  | .ramHammingWeightBooleanity => true
  | _ => false

end JoltConstraints
