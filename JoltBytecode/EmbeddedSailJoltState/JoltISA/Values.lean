import JoltBytecode.EmbeddedSailJoltState.JoltISA.Operands

/-!
# Pure Jolt ISA values

These definitions are the non-monadic value computations shared by the
instruction semantics and the equivalence proofs.
-/

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-- RV64 `VirtualMovsign` value: all ones if the source sign bit is set,
otherwise zero. -/
def jolt_movsign_value (x : BitVec 64) : BitVec 64 :=
  if x.msb then (-1 : BitVec 64) else 0

/-- RV64 `MULHU` value: high 64 bits of the unsigned 64x64 product. -/
def jolt_mulhu_value (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat * y.toNat / 2^64)

/-- If a 64-bit word is below `2^63`, `VirtualMovsign` returns zero. -/
theorem jolt_movsign_value_eq_zero_of_toNat_lt_half (x : BitVec 64)
    (h : x.toNat < 9223372036854775808) :
    jolt_movsign_value x = 0 := by
  unfold jolt_movsign_value
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false_iff_not.mpr (by omega)
  rw [hmsb]
  rfl

/-- If a 64-bit word is at least `2^63`, `VirtualMovsign` returns all ones. -/
theorem jolt_movsign_value_eq_neg_one_of_half_le (x : BitVec 64)
    (h : ¬ x.toNat < 9223372036854775808) :
    jolt_movsign_value x = (-1 : BitVec 64) := by
  unfold jolt_movsign_value
  have hmsb : x.msb = true := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_true_eq.mpr (by omega)
  rw [hmsb]
  rfl

/-- RV64 `SLTU` value: one if `x < y` as unsigned 64-bit integers,
otherwise zero. -/
def jolt_sltu_value (x y : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y))

/-- `SLTU` returns one when the unsigned comparison is true. -/
theorem jolt_sltu_value_eq_one_of_lt (x y : BitVec 64)
    (h : x.toNat < y.toNat) :
    jolt_sltu_value x y = 1 := by
  unfold jolt_sltu_value zopz0zI_u BitVec.toNatInt bool_to_bit
    bool_bit_forwards zero_extend
  simp [h]
  decide

/-- `SLTU` returns zero when the unsigned comparison is false. -/
theorem jolt_sltu_value_eq_zero_of_not_lt (x y : BitVec 64)
    (h : ¬ x.toNat < y.toNat) :
    jolt_sltu_value x y = 0 := by
  unfold jolt_sltu_value zopz0zI_u BitVec.toNatInt bool_to_bit
    bool_bit_forwards zero_extend
  simp [h]
  decide

/-- The natural-number value of `jolt_sltu_value` is the expected Boolean flag,
viewed as `0` or `1`. -/
theorem jolt_sltu_value_toNat (x y : BitVec 64) :
    (jolt_sltu_value x y).toNat = if x.toNat < y.toNat then 1 else 0 := by
  by_cases h : x.toNat < y.toNat
  · rw [jolt_sltu_value_eq_one_of_lt x y h]
    simp [h]
  · rw [jolt_sltu_value_eq_zero_of_not_lt x y h]
    simp [h]

/-- Upper 64 bits of a signed 64×64 multiply. -/
def mulhs (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((a.toInt * b.toInt) / (2 ^ 64))

end
