import JoltConstraints.ConstraintCompleteness.Encoding

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem rightInstructionInputEqSelectedOperands
    {params : JoltWitnessParams} {F : Type u} [Field F]
    (trace : HonestTrace params) :
    JoltConstraint.Satisfied .rightInstructionInputEqSelectedOperands
      trace.metadata.toJoltPublicInputs
      (honest_witness (F := F) trace) := by
  unfold JoltConstraint.Satisfied
  intro i
  let row := trace.rows i
  have valid : JoltTraceRow.Valid trace.metadata.toJoltPublicInputs row
      (trace.preState i) (trace.postState i) := by
    simpa [row, HonestTrace.preState, HonestTrace.postState] using
      trace.rowValid i
  have rowPackable : row.instructionRow.operands.Packable := by
    have tablePackable :=
      trace.metadataValid.publicInputsValid.bytecodeRowsPackable
        ⟨row.metadata.pc, valid.pcBound⟩
    rw [valid.bytecodeRow_eq valid.pcBound] at tablePackable
    exact tablePackable.1
  have immAbsBound :
      (row.instructionRow.operands.imm.natAbs : Int) <
        (2 : Int) ^ Xlen := by
    exact_mod_cast rowPackable
  have immUpper64 :
      row.instructionRow.operands.imm < (2 : Int) ^ Xlen := by
    exact lt_of_le_of_lt Int.le_natAbs immAbsBound
  have immLower64 :
      -(2 : Int) ^ Xlen < row.instructionRow.operands.imm := by
    have neg_le :
        -row.instructionRow.operands.imm ≤
          (row.instructionRow.operands.imm.natAbs : Int) := by
      simpa using (Int.le_natAbs
        (a := -row.instructionRow.operands.imm))
    omega
  have immUpper128 :
      row.instructionRow.operands.imm <
        (2 : Int) ^ (InstructionLookupAddressBits - 1) := by
    norm_num [Xlen, InstructionLookupAddressBits] at immUpper64 ⊢
    omega
  have immLower128 :
      -(2 : Int) ^ (InstructionLookupAddressBits - 1) ≤
        row.instructionRow.operands.imm := by
    norm_num [Xlen, InstructionLookupAddressBits] at immLower64 ⊢
    omega
  have lowImmediateValue :
      HonestWitness.fieldFromI128 (F := F)
          ((HonestWitness.lowImmediate row).getD 0) =
        HonestWitness.fieldBool
            (HonestWitness.rightOperandIsImmediate row.instruction) *
          HonestWitness.fieldFromInt (F := F)
            row.instructionRow.operands.imm := by
    generalize instruction_eq : row.instruction = instruction
    cases instruction <;>
      simp only [HonestWitness.lowImmediate,
        HonestWitness.rightOperandIsImmediate,
        HonestWitness.signedInstructionImmediate,
        HonestWitness.fieldBool, instruction_eq,
        Option.getD, Bool.false_eq_true, eq_self,
        if_false, if_true, zero_mul, one_mul,
        fieldFromI128_zero]
    all_goals first
      | exact fieldFromI128_ofInt_eq_fieldFromInt
          _ immLower128 immUpper128
      | apply fieldFromI128_zeroExtendedInt_eq_fieldFromInt
        · have immediateMatches := valid.instructionImmediate_eq
          simp [HonestWitness.instructionImmediateMatches,
            HonestWitness.instructionImmediate, instruction_eq] at immediateMatches
          omega
        · exact immUpper64
  change
    HonestWitness.fieldFromI128 (F := F)
          (HonestWitness.instructionInputs row).2 -
        (HonestWitness.fieldBool
              ((HonestWitness.lookupSecondSource row.instruction).isSome) *
            HonestWitness.fieldFromU64 (F := F) row.rs2Value +
          HonestWitness.fieldBool
              (HonestWitness.rightOperandIsImmediate row.instruction) *
            HonestWitness.fieldFromInt (F := F)
              row.instructionRow.operands.imm) = 0
  simp only [HonestWitness.instructionInputs]
  split
  · rename_i secondSourcePresent
    have immediateFalse :
        HonestWitness.rightOperandIsImmediate row.instruction = false := by
      generalize instruction_eq : row.instruction = instruction at secondSourcePresent ⊢
      cases instruction <;>
        simp [HonestWitness.lookupSecondSource, HonestWitness.secondSource,
          HonestWitness.rightOperandIsImmediate] at secondSourcePresent ⊢
    rw [fieldFromI128_zeroExtendedU64_eq_fieldFromU64]
    simp [secondSourcePresent, immediateFalse, HonestWitness.fieldBool]
  · rename_i secondSourceAbsent
    rw [lowImmediateValue]
    simp [secondSourceAbsent, HonestWitness.fieldBool]

end JoltConstraints.JoltConstraint.Completeness
