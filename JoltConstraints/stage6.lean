import JoltConstraints.constraints

namespace JoltConstraints

/-!
`stage6` classifies the coefficient-level witness identities inside Rust's
booleanity, instruction/RAM virtualization, RAM hamming-booleanity, and
fixed/public bytecode read-RAF relations. Rust gamma-batches families and
splits the bytecode relation over address and cycle rounds; this classifier
does not turn those components into separate sumchecks.

Claim reductions remain outside this witness-constraint classifier.
-/

def stage6 : JoltConstraint → Bool
  | .instructionRaBooleanity
  | .bytecodeRaBooleanity
  | .ramRaBooleanity
  | .instructionRaVirtualization
  | .ramRaVirtualization
  | .ramHammingWeightBooleanity
  | .unexpandedPCEqBytecodeReadRaf
  | .immEqBytecodeReadRaf
  | .circuitFlagsEqBytecodeReadRaf
  | .pcEqBytecodeReadRafAddress
  | .instructionFlagsEqBytecodeReadRaf
  | .rs1RaEqBytecodeReadRaf
  | .rs2RaEqBytecodeReadRaf
  | .rdWaEqBytecodeReadRaf
  | .instructionRafFlagEqBytecodeReadRaf
  | .lookupTableFlagsEqBytecodeReadRaf
  | .initialBytecodeRaEqEntry => true
  | _ => false

end JoltConstraints
