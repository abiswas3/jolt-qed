import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

theorem lookupOutput_eq_boolU64_of_isBranch
    (row : JoltTraceRow)
    (isBranch : HonestWitness.isBranch row.instruction = true) :
    ∃ value : Bool,
      HonestWitness.lookupOutput row =
        HonestWitness.boolU64 value := by
  rcases row with ⟨instruction, metadata, captured⟩
  cases instruction <;> cases captured <;>
    simp_all [HonestWitness.isBranch, HonestWitness.lookupOutput,
      HonestWitness.writesLookupOutput, HonestWitness.destination,
      HonestWitness.boolU64] <;>
    first | omega | tauto

theorem isJump_eq_false_of_shouldBranch_eq_true
    (row : JoltTraceRow) (shouldBranch : row.shouldBranch = true) :
    HonestWitness.isJump row.instruction = false := by
  cases h : row.instruction <;>
    simp_all [JoltTraceRow.shouldBranch, HonestWitness.isBranch,
      HonestWitness.isJump]

end JoltConstraints.JoltConstraint.Completeness
