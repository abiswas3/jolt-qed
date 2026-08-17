import JoltConstraints.constraints
import JoltConstraints.trace

namespace JoltConstraints.JoltConstraint.Completeness

universe u

theorem zeroExtendedU64_msb_false (value : HonestWitness.U64) :
    (BitVec.ofNat InstructionLookupAddressBits value.toNat).msb =
      false := by
  rw [BitVec.ofNat_toNat, BitVec.msb_setWidth]
  norm_num [InstructionLookupAddressBits]

@[simp] theorem low64_setWidthU64 (value : HonestWitness.U64) :
    HonestWitness.low64
        (value.setWidth InstructionLookupAddressBits) = value := by
  apply BitVec.eq_of_toNat_eq
  simp only [HonestWitness.low64, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]
  have value_lt_wide :
      value.toNat < 2 ^ InstructionLookupAddressBits :=
    lt_trans value.isLt (by
      norm_num [InstructionLookupAddressBits, Xlen])
  rw [Nat.mod_eq_of_lt value_lt_wide, Nat.mod_eq_of_lt value.isLt]

@[simp] theorem setWidthU64_toInt (value : HonestWitness.U64) :
    (value.setWidth InstructionLookupAddressBits).toInt =
      (value.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp
  · simpa only [BitVec.ofNat_toNat] using zeroExtendedU64_msb_false value

@[simp] theorem u64_toNat_intEmod_instructionWidth
    (value : HonestWitness.U64) :
    (value.toNat : Int) % (2 ^ InstructionLookupAddressBits : Int) =
      value.toNat := by
  rw [Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · exact_mod_cast lt_trans value.isLt (by
      norm_num [InstructionLookupAddressBits, Xlen])

@[simp] theorem u64_toNat_intEmod_xlen
    (value : HonestWitness.U64) :
    (value.toNat : Int) % (2 ^ Xlen : Int) = value.toNat := by
  rw [Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · exact_mod_cast value.isLt

@[simp] theorem u64_toNat_intBmod_instructionWidth
    (value : HonestWitness.U64) :
    (value.toNat : Int).bmod (2 ^ InstructionLookupAddressBits) =
      value.toNat := by
  rw [Int.bmod_eq_of_le]
  · norm_num [InstructionLookupAddressBits, Xlen]
  · have value_lt := value.isLt
    norm_num [InstructionLookupAddressBits, Xlen] at value_lt ⊢
    omega

@[simp] theorem zeroExtendedU64_toNat_lt (value : HonestWitness.U64) :
    (BitVec.ofNat InstructionLookupAddressBits value.toNat).toNat <
      2 ^ Xlen := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · exact value.isLt
  · exact lt_trans value.isLt (by
      norm_num [InstructionLookupAddressBits, Xlen])

theorem fieldFromU128_zeroExtendedU64_eq_fieldFromI128
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits value.toNat) =
      HonestWitness.fieldFromI128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits value.toNat) := by
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromI128
  rw [BitVec.toInt_eq_toNat_of_msb (zeroExtendedU64_msb_false value)]
  simp

@[simp] theorem fieldFromI128_zeroExtendedU64_eq_fieldFromU64
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromI128 (F := F)
        (BitVec.ofNat InstructionLookupAddressBits value.toNat) =
      HonestWitness.fieldFromU64 (F := F) value := by
  rw [← fieldFromU128_zeroExtendedU64_eq_fieldFromI128]
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromU64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_trans value.isLt (by
    norm_num [InstructionLookupAddressBits, Xlen])

@[simp] theorem fieldFromI128_setWidthU64_eq_fieldFromU64
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromI128 (F := F)
        (value.setWidth InstructionLookupAddressBits) =
      HonestWitness.fieldFromU64 (F := F) value := by
  simpa only [BitVec.ofNat_toNat] using
    fieldFromI128_zeroExtendedU64_eq_fieldFromU64 (F := F) value

@[simp] theorem fieldFromU128_setWidthU64_eq_fieldFromU64
    {F : Type u} [Field F] (value : HonestWitness.U64) :
    HonestWitness.fieldFromU128 (F := F)
        (value.setWidth InstructionLookupAddressBits) =
      HonestWitness.fieldFromU64 (F := F) value := by
  calc
    HonestWitness.fieldFromU128 (F := F)
        (value.setWidth InstructionLookupAddressBits) =
        HonestWitness.fieldFromI128 (F := F)
          (value.setWidth InstructionLookupAddressBits) := by
      simpa only [BitVec.ofNat_toNat] using
        fieldFromU128_zeroExtendedU64_eq_fieldFromI128 (F := F) value
    _ = HonestWitness.fieldFromU64 (F := F) value := by simp

theorem fieldFromU128_setWidthLow64_eq_fieldFromI128_of_lt
    {F : Type u} [Field F] (value : HonestWitness.U128)
    (value_lt : value.toNat < 2 ^ Xlen) :
    HonestWitness.fieldFromU128 (F := F)
        ((HonestWitness.low64 value).setWidth
          InstructionLookupAddressBits) =
      HonestWitness.fieldFromI128 (F := F) value := by
  have roundtrip :
      (HonestWitness.low64 value).setWidth
          InstructionLookupAddressBits = value := by
    apply BitVec.eq_of_toNat_eq
    simp only [HonestWitness.low64, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt value_lt]
    rw [Nat.mod_eq_of_lt]
    norm_num [Xlen, InstructionLookupAddressBits] at value_lt ⊢
    omega
  have value_msb : value.msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    have width_bound : 2 ^ Xlen < 2 ^ (InstructionLookupAddressBits - 1) := by
      norm_num [Xlen, InstructionLookupAddressBits]
    have : value.toNat < 2 ^ (InstructionLookupAddressBits - 1) :=
      lt_trans value_lt width_bound
    norm_num [InstructionLookupAddressBits] at this ⊢
    omega
  rw [roundtrip]
  unfold HonestWitness.fieldFromU128 HonestWitness.fieldFromI128
  rw [BitVec.toInt_eq_toNat_of_msb value_msb]
  simp

theorem fieldFromU64_low64_eq_fieldFromI128_of_lt
    {F : Type u} [Field F] (value : HonestWitness.U128)
    (value_lt : value.toNat < 2 ^ Xlen) :
    HonestWitness.fieldFromU64 (F := F) (HonestWitness.low64 value) =
      HonestWitness.fieldFromI128 (F := F) value := by
  calc
    HonestWitness.fieldFromU64 (F := F) (HonestWitness.low64 value) =
        HonestWitness.fieldFromU128 (F := F)
          ((HonestWitness.low64 value).setWidth
            InstructionLookupAddressBits) := by
      symm
      exact fieldFromU128_setWidthU64_eq_fieldFromU64
        (HonestWitness.low64 value)
    _ = HonestWitness.fieldFromI128 (F := F) value :=
      fieldFromU128_setWidthLow64_eq_fieldFromI128_of_lt value value_lt

end JoltConstraints.JoltConstraint.Completeness
