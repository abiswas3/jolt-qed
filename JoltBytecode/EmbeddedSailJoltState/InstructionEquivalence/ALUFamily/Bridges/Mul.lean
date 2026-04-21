import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import Mathlib

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Bridges for multiplicative W-variants

Three facts in this file:

* `extractLsb_mul` — `(a *₆₄ b)[31:0] = a[31:0] *₃₂ b[31:0]`. The direct
  analogue of `extractLsb_add`.

* `mulw32_eq_mul` — a transcription-level fact connecting the Sail
  transpilation's `to_bits_truncate ∘ (·*i·) ∘ toInt ∘ extractLsb`
  expression to the plain 32-bit `BitVec` multiply. The Sail generator
  emits the former; the natural Jolt expression is the latter.

* Private helpers `mod33_toNat_mod32`, `trunc32_eq_intCast`, and
  `intCast_mul_toInt_32` that feed into `mulw32_eq_mul`.
-/

private theorem mod33_toNat_mod32 (x : Int) :
    (x % 8589934592).toNat % 4294967296 = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32 x

private theorem intCast_mul_toInt_32 (a b : BitVec 32) :
    (((BitVec.toInt a *i BitVec.toInt b : Int) : BitVec 32)) = a * b := by
  change BitVec.ofInt 32 (a.toInt * b.toInt) = a * b
  rw [BitVec.ofInt_mul]
  have h1 : BitVec.ofInt 32 a.toInt = a := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  have h2 : BitVec.ofInt 32 b.toInt = b := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toInt]; omega
  rw [h1, h2]

/-- The Sail transpilation's `MULW` value expression (truncating an
unbounded `Int` product of the `toInt`s) equals the plain 32-bit
`BitVec` product. -/
theorem mulw32_eq_mul (a b : BitVec 32) :
    to_bits_truncate (l := 32) (BitVec.toInt a *i BitVec.toInt b) = a * b := by
  rw [trunc32_eq_intCast]
  exact intCast_mul_toInt_32 a b

/-- `(a *₆₄ b)[31:0] = a[31:0] *₃₂ b[31:0]`. -/
theorem extractLsb_mul (v1 v2 : BitVec 64) :
    Sail.BitVec.extractLsb (v1 * v2) 31 0 =
      Sail.BitVec.extractLsb v1 31 0 * Sail.BitVec.extractLsb v2 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

end
