import JoltBytecode.EmbeddedSailJoltState.JoltISA.Operands
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs

/-!
# Pure Jolt ISA values

These definitions are the non-monadic value computations shared by the
instruction semantics and the equivalence proofs.
This makes it easier to describe the instruction semantics for writing and reading.

Sometimes it's also helpful to have mini theorems about this computations.
It helps while proving things.
-/

/- set_option maxHeartbeats 1_000_000_000 -/
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

/-- RV64 `VirtualMULI` value: multiply by the immediate in the 64-bit word
ring.  In the Rust tracer this instruction writes the sign-extended machine
word after a wrapping multiply; for RV64 that is exactly the resulting
64-bit bit pattern. -/
def jolt_virtual_muli_value (x imm : BitVec 64) : BitVec 64 :=
  x * imm

/-- RV64 `VirtualPow2` value: `2 ^ (x[5:0])`, used by `SLL`. -/
def jolt_virtual_pow2_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 6).toNat)

/-- RV64 `VirtualPow2W` value: `2 ^ (x[4:0])`, used by `SLLW`. -/
def jolt_virtual_pow2w_value (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ (x.setWidth 5).toNat)

/-- RV64 `VirtualShiftRightBitmask` value.

The tracer first masks the requested shift to six bits, then writes a word
whose trailing-zero count is exactly that shift.  Later `VirtualSRL` and
`VirtualSRA` consume this bitmask by taking `ctz`. -/
def jolt_virtual_shift_right_bitmask_value (x : BitVec 64) : BitVec 64 :=
  let shift := (x.setWidth 6).toNat
  let ones := (1 <<< (64 - shift)) - 1
  BitVec.ofNat 64 (ones <<< shift)

/-- The natural-number bitmask encoded by `VirtualShiftRightBitmask` fits in
64 bits.  This justifies reading the produced `BitVec 64` back as a `Nat`
without changing the trailing-zero structure consumed by `VirtualSRL` and
`VirtualSRA`. -/
private theorem jolt_virtual_shift_right_bitmask_nat_lt (x : BitVec 64) :
    (let shift := (x.setWidth 6).toNat
     let ones := (1 <<< (64 - shift)) - 1
     ones <<< shift) < 2 ^ 64 := by
  simp only [Nat.shiftLeft_eq]
  set shift := (x.setWidth 6).toNat
  have hshift_lt : shift < 64 := by
    have := (x.setWidth 6).isLt
    norm_num at this
    exact this
  have hdiff_pos : 0 < 64 - shift := by omega
  have hones_lt : 2 ^ (64 - shift) - 1 < 2 ^ (64 - shift) := by
    have hpow_pos : 0 < 2 ^ (64 - shift) := by positivity
    omega
  have hmul_lt :
      (2 ^ (64 - shift) - 1) * 2 ^ shift <
        2 ^ (64 - shift) * 2 ^ shift :=
    Nat.mul_lt_mul_of_pos_right hones_lt (by positivity)
  have hpow : 2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  simpa [hpow] using hmul_lt

/-- Reading back the `VirtualShiftRightBitmask` result as a natural number
recovers the same encoded bitmask used in the Rust expansion. -/
theorem jolt_virtual_shift_right_bitmask_value_toNat (x : BitVec 64) :
    (jolt_virtual_shift_right_bitmask_value x).toNat =
      (let shift := (x.setWidth 6).toNat
       let ones := (1 <<< (64 - shift)) - 1
       ones <<< shift) := by
  unfold jolt_virtual_shift_right_bitmask_value
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact jolt_virtual_shift_right_bitmask_nat_lt x

/-- The essential contract of `VirtualShiftRightBitmask`: the word it writes
has exactly `x[5:0]` trailing zeroes.  `VirtualSRL` and `VirtualSRA` consume
only this `ctz` value, so this lemma is the reusable bridge from the virtual
instruction to ordinary Sail shifts. -/
theorem ctz_jolt_virtual_shift_right_bitmask_value (x : BitVec 64) :
    ctz (jolt_virtual_shift_right_bitmask_value x).toNat =
      (x.setWidth 6).toNat := by
  rw [jolt_virtual_shift_right_bitmask_value_toNat]
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := (x.setWidth 6).toNat
  have h_lt : shift < 64 := by
    have := (x.setWidth 6).isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos,
    ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

/-- RV64 `VirtualSRLI` value: logical right shift by the trailing-zero count
of the encoded bitmask immediate. -/
def jolt_virtual_srli_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x >>> ctz bitmask

/-- RV64 `VirtualSRAI` value: arithmetic right shift by the trailing-zero
count of the encoded bitmask immediate. -/
def jolt_virtual_srai_value (x : BitVec 64) (bitmask : Nat) : BitVec 64 :=
  x.sshiftRight (ctz bitmask)

/-- RV64 `VirtualSRL` value: logical right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_srl_value (x bitmask : BitVec 64) : BitVec 64 :=
  x >>> ctz bitmask.toNat

/-- RV64 `VirtualSRA` value: arithmetic right shift by `ctz` of the bitmask
stored in the second source register. -/
def jolt_virtual_sra_value (x bitmask : BitVec 64) : BitVec 64 :=
  x.sshiftRight (ctz bitmask.toNat)

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
