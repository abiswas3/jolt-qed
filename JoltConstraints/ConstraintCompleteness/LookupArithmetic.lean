import JoltConstraints.ConstraintCompleteness.Encoding

namespace JoltConstraints.JoltConstraint.Completeness

universe u

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
