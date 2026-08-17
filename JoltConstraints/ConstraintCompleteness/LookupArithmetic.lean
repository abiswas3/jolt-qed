import JoltConstraints.ConstraintCompleteness.Encoding

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem fieldFromU128_ofInt_add
    {F : Type u} [Field F]
    (left : HonestWitness.U64) (right : HonestWitness.U128)
    (nonnegative : 0 ≤ (left.toNat : Int) + right.toInt) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofInt InstructionLookupAddressBits
          ((left.toNat : Int) + right.toInt)) =
      HonestWitness.fieldFromU64 (F := F) left +
        HonestWitness.fieldFromI128 (F := F) right := by
  have left_lt : (left.toNat : Int) < 2 ^ Xlen := by
    exact_mod_cast left.isLt
  have right_lt : right.toInt < 2 ^ (InstructionLookupAddressBits - 1) :=
    BitVec.toInt_lt
  have sum_lt :
      (left.toNat : Int) + right.toInt <
        2 ^ InstructionLookupAddressBits := by
    norm_num [Xlen, InstructionLookupAddressBits] at left_lt right_lt ⊢
    omega
  have sum_lt' :
      (left.toNat : Int) + right.toInt <
        ((2 ^ InstructionLookupAddressBits : Nat) : Int) := by
    norm_num [InstructionLookupAddressBits] at sum_lt ⊢
    exact sum_lt
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
    HonestWitness.fieldFromI128
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt nonnegative sum_lt']
  have cast_nonnegative :=
    congrArg (fun value : Int => (value : F))
      (Int.toNat_of_nonneg nonnegative)
  simpa only [Int.cast_add, Int.cast_natCast] using cast_nonnegative

theorem fieldFromU128_addU64
    {F : Type u} [Field F]
    (left right : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits
          (left.toNat + right.toNat)) =
      HonestWitness.fieldFromU64 (F := F) left +
        HonestWitness.fieldFromU64 (F := F) right := by
  have sum_lt :
      left.toNat + right.toNat < 2 ^ InstructionLookupAddressBits := by
    have left_lt := left.isLt
    have right_lt := right.isLt
    norm_num [Xlen, InstructionLookupAddressBits] at left_lt right_lt ⊢
    omega
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sum_lt, Nat.cast_add]

theorem fieldFromU128_addLow64
    {F : Type u} [Field F]
    (left : HonestWitness.U64) (right : HonestWitness.U128)
    (right_lt : right.toNat < 2 ^ Xlen) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits
          (left.toNat + (HonestWitness.low64 right).toNat)) =
      HonestWitness.fieldFromU64 (F := F) left +
        HonestWitness.fieldFromI128 (F := F) right := by
  rw [fieldFromU128_addU64,
    fieldFromU64_low64_eq_fieldFromI128_of_lt right right_lt]

theorem addOperands_are_exclusive
    (instruction : JoltISA.Instr)
    (isAdd : HonestWitness.addOperands instruction = true) :
    HonestWitness.adviceOperands instruction = false ∧
      HonestWitness.subtractOperands instruction = false ∧
      HonestWitness.multiplyOperands instruction = false := by
  cases instruction <;>
    simp_all [HonestWitness.addOperands, HonestWitness.adviceOperands,
      HonestWitness.subtractOperands, HonestWitness.multiplyOperands]

theorem zeroExtended_mod_xlen_lt (value : Nat) :
    (BitVec.ofNat InstructionLookupAddressBits
      (value % 2 ^ Xlen)).toNat < 2 ^ Xlen := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · exact Nat.mod_lt _ (by positivity)
  · exact lt_trans (Nat.mod_lt _ (by positivity)) (by
      norm_num [Xlen, InstructionLookupAddressBits])

theorem addInput_right_lt_of_unsigned
    (row : JoltTraceRow)
    (isAdd : HonestWitness.addOperands row.instruction = true)
    (isUnsigned : HonestWitness.signedInstructionImmediate row.instruction = false) :
    (HonestWitness.instructionInputs row).2.toNat < 2 ^ Xlen := by
  cases h : row.instruction <;>
    simp_all [HonestWitness.addOperands,
      HonestWitness.signedInstructionImmediate,
      HonestWitness.instructionInputs, HonestWitness.leftIsPC,
      HonestWitness.lookupFirstSource, HonestWitness.lookupSecondSource,
      HonestWitness.firstSource, HonestWitness.secondSource,
      HonestWitness.lowImmediate, HonestWitness.rightOperandIsImmediate,
      HonestWitness.instructionImmediate] <;>
    first
    | exact (row.rs2Value).isLt
    | exact (row.rs1Value).isLt
    | exact BitVec.isLt _
    | exact zeroExtended_mod_xlen_lt _

theorem fieldFrom_addLookup
    {F : Type u} [Field F]
    (row : JoltTraceRow)
    (isAdd : HonestWitness.addOperands row.instruction = true)
    (nonnegative :
      0 ≤ ((HonestWitness.instructionInputs row).1.toNat : Int) +
        (HonestWitness.instructionInputs row).2.toInt) :
    HonestWitness.fieldFromU128 (F := F)
        (HonestWitness.lookupOperands row).2 =
      HonestWitness.fieldFromU64 (F := F)
          (HonestWitness.instructionInputs row).1 +
        HonestWitness.fieldFromI128 (F := F)
          (HonestWitness.instructionInputs row).2 := by
  obtain ⟨notAdvice, notSub, notMul⟩ :=
    addOperands_are_exclusive row.instruction isAdd
  unfold HonestWitness.lookupOperands
  simp only [notAdvice, notSub, notMul, isAdd, Bool.false_eq_true,
    ↓reduceIte]
  split
  · exact fieldFromU128_ofInt_add
      (HonestWitness.instructionInputs row).1
      (HonestWitness.instructionInputs row).2 nonnegative
  · have isUnsigned :
        HonestWitness.signedInstructionImmediate row.instruction = false := by
      cases hvalue : HonestWitness.signedInstructionImmediate row.instruction <;>
        simp_all
    exact fieldFromU128_addLow64
      (HonestWitness.instructionInputs row).1
      (HonestWitness.instructionInputs row).2
      (addInput_right_lt_of_unsigned row isAdd isUnsigned)

theorem fieldFromU128_subLookup
    {F : Type u} [Field F]
    (left right : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits
          (left.toNat + 2 ^ Xlen - right.toNat)) =
      HonestWitness.fieldFromU64 (F := F) left +
        ((2 ^ Xlen : Nat) : F) -
        HonestWitness.fieldFromU64 (F := F) right := by
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · rw [Nat.cast_sub]
    · simp
    · exact le_trans (Nat.le_of_lt right.isLt) (Nat.le_add_left _ _)
  · have left_lt := left.isLt
    have right_lt := right.isLt
    norm_num [InstructionLookupAddressBits, Xlen] at left_lt right_lt ⊢
    omega

@[simp] theorem fieldFromU128_mulU64
    {F : Type u} [Field F]
    (left right : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits
          (left.toNat * right.toNat)) =
      HonestWitness.fieldFromU64 (F := F) left *
        HonestWitness.fieldFromU64 (F := F) right := by
  have product_lt :
      left.toNat * right.toNat < 2 ^ InstructionLookupAddressBits := by
    by_cases right_zero : right.toNat = 0
    · simp [right_zero, InstructionLookupAddressBits]
    · calc
        left.toNat * right.toNat < (2 ^ Xlen) * right.toNat :=
          mul_lt_mul_of_pos_right left.isLt (Nat.pos_of_ne_zero right_zero)
        _ < (2 ^ Xlen) * (2 ^ Xlen) :=
          mul_lt_mul_of_pos_left right.isLt (by positivity)
        _ = 2 ^ InstructionLookupAddressBits := by
          norm_num [InstructionLookupAddressBits, Xlen]
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt product_lt]
  simp

@[simp] theorem fieldFromU128_low64_zeroExtendedU64_eq_fieldFromI128
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits
          (HonestWitness.low64
            (BitVec.ofNat InstructionLookupAddressBits value.toNat)).toNat) =
      HonestWitness.fieldFromI128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits value.toNat) := by
  have low64_eq :
      HonestWitness.low64
          (BitVec.ofNat InstructionLookupAddressBits value.toNat) = value := by
    apply BitVec.eq_of_toNat_eq
    simp [HonestWitness.low64, InstructionLookupAddressBits, Xlen]
    exact value.isLt
  rw [low64_eq]
  exact fieldFromU128_zeroExtendedU64_eq_fieldFromI128 value

@[simp] theorem fieldFromU128_setWidthLow64_zeroExtendedU64_eq_fieldFromI128
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        ((HonestWitness.low64
          (BitVec.ofNat InstructionLookupAddressBits value.toNat)).setWidth
            InstructionLookupAddressBits) =
      HonestWitness.fieldFromI128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits value.toNat) := by
  rw [← BitVec.ofNat_toNat]
  exact fieldFromU128_low64_zeroExtendedU64_eq_fieldFromI128 value

@[simp] theorem fieldFromU128_low64_zero_eq_fieldFromI128_zero
    {F : Type u} [Field F] :
    HonestWitness.fieldFromU128 (F := F)
        ((HonestWitness.low64 (0 : HonestWitness.U128)).setWidth
          InstructionLookupAddressBits) =
      HonestWitness.fieldFromI128 (F := F) (0 : HonestWitness.U128) := by
  simp [HonestWitness.low64, HonestWitness.fieldFromU128,
    HonestWitness.fieldFromI128]

@[simp] theorem fieldFromU128_low64_setWidthU64_eq_fieldFromI128
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        ((HonestWitness.low64
          (value.setWidth InstructionLookupAddressBits)).setWidth
            InstructionLookupAddressBits) =
      HonestWitness.fieldFromI128 (F := F)
        (value.setWidth InstructionLookupAddressBits) := by
  simpa only [BitVec.ofNat_toNat] using
    (fieldFromU128_low64_zeroExtendedU64_eq_fieldFromI128
      (F := F) value)

@[simp] theorem fieldFromU64_low64_setWidthU64_eq_fieldFromI128
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU64 (F := F)
        (HonestWitness.low64
          (value.setWidth InstructionLookupAddressBits)) =
      HonestWitness.fieldFromI128 (F := F)
        (value.setWidth InstructionLookupAddressBits) := by
  rw [low64_setWidthU64]
  simpa only [BitVec.ofNat_toNat] using
    (fieldFromI128_zeroExtendedU64_eq_fieldFromU64 (F := F) value).symm

end JoltConstraints.JoltConstraint.Completeness
