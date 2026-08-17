import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

theorem lookupOutput_eq_boolU64_of_isBranch
    (instruction : JoltISA.Instr)
    (metadata : JoltTraceRowMetadata)
    (before after : SailJoltState)
    (isBranch : HonestWitness.isBranch instruction = true) :
    ∃ value : Bool,
      HonestWitness.lookupOutput instruction metadata before after =
        HonestWitness.boolU64 value := by
  cases instruction <;>
    simp_all [HonestWitness.isBranch, HonestWitness.lookupOutput,
      HonestWitness.writesLookupOutput, HonestWitness.destination,
      HonestWitness.boolU64] <;>
    first | omega | tauto

end JoltConstraints.JoltConstraint.Completeness
