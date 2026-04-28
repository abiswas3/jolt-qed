import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divuw_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `jolt_divuw` (advice-verified DIVUW)

The DIVUW counterpart of `Div_math.lean` / `Divu_math.lean` /
`Divw_math.lean`. Provides:

* The honest-advice value `sail_divuw_advice` — the u32 quotient
  zero-extended into a 64-bit BitVec. After sign-extension this equals
  `sail_divw_value dividend divisor true` (the value Sail writes to
  `rd`).
* Four **honest-advice guard lemmas** corresponding to the four
  asserts in `jolt_divuw`'s inline sequence.
* The **uniqueness lemma** `advice_unique_of_guards_uw`.
* The **sign-extension round-trip** lemma
  `sext_advice_eq_sail_divw_value` — used by `jolt_divuw_concrete`'s
  writeback step to convert the post-state's `sext(q)` into
  `sail_divw_value`.

All statements are sorried.
-/

-- ----------------------------------------------------------------------------
-- Honest advice value
-- ----------------------------------------------------------------------------

/-- The honest oracle quotient for DIVUW: the unsigned 32-bit quotient
of `(dividend low 32 bits) / (divisor low 32 bits)`, zero-extended to
64 bits. Equals `u32::MAX` (zero-extended to `0x00000000FFFFFFFF`) when
the divisor is zero. After sign-extension this becomes
`sail_divw_value dividend divisor true`. -/
def sail_divuw_advice (dividend divisor : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64)
    (Sail.BitVec.extractLsb (sail_divw_value dividend divisor true) 31 0)

-- ----------------------------------------------------------------------------
-- Sign-extension round-trip
-- ----------------------------------------------------------------------------

/-- The honest advice round-trips through `sign_extend ∘ extractLsb 31 0`
to give `sail_divw_value`. Used by `jolt_divuw_concrete`'s writeback
step. -/
theorem sext_advice_eq_sail_divw_value (dividend divisor : BitVec 64) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sail_divuw_advice dividend divisor) 31 0)
      = sail_divw_value dividend divisor true := by
  sorry

-- ----------------------------------------------------------------------------
-- Honest-advice guards
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertMulUNoOverflow v2 v1`.**

`q × zext_divisor` doesn't overflow 64 bits unsigned: `q` is a u32 (so
`q.toNat < 2^32`) and `zext_divisor.toNat < 2^32`, hence the product is
< `2^64`. -/
theorem hguard_no_overflow_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    q.toNat * zv.toNat < 2^64 := by
  sorry

/-- **Guard 2 — `VirtualAssertLTE v3 v0`.**

The unsigned division identity: for non-zero divisor,
`q × zext_divisor ≤ zext_dividend`. For zero divisor `q = u32::MAX`
but `q × 0 = 0 ≤ zext_dividend`. -/
theorem hguard_q_times_d_le_dividend_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    (q * zv).toNat ≤ zd.toNat := by
  sorry

/-- **Guard 3 — `VirtualAssertValidUnsignedRemainder v3 v1`.**

Either `zext_divisor = 0` (vacuous) or
`(zext_dividend − q × zext_divisor).toNat < zext_divisor.toNat`. -/
theorem hguard_rem_bound_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat := by
  sorry

/-- **Guard 4 — `VirtualAssertValidDiv0 v1 v3` (on sign-extended quotient).**

When the (zero-extended) divisor is zero, the spec forces
`q = u32::MAX`, whose sign-extension to 64 bits is `-1`. -/
theorem hguard_div0_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    ¬ (zv = 0#64 ∧
       sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) := by
  sorry

-- ----------------------------------------------------------------------------
-- Soundness uniqueness
-- ----------------------------------------------------------------------------

/-- **Soundness uniqueness.** If the four guards hold for some advice
`q`, then `q = sail_divuw_advice dividend divisor` (the unique honest
u32 quotient, zero-extended).

DIVUW analogue of `advice_unique_of_guards_u`. The proof plan splits
on `zv = 0` (forces `sext(q) = -1`, i.e. `q.low_32 = u32::MAX`, plus
upper bits constrained to 0 by the no-overflow guard with `zv` already
in u32 range) and the normal case (unsigned u32 uniqueness of the
truncating quotient with `0 ≤ rem < zv`). -/
theorem advice_unique_of_guards_uw
    (dividend divisor q : BitVec 64)
    (h1 : q.toNat *
            (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
          < 2^64)
    (h2 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      (q * zv).toNat ≤ zd.toNat)
    (h3 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat)
    (h4 :
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      ¬ (zv = 0#64 ∧
         sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64))) :
    q = sail_divuw_advice dividend divisor := by
  sorry

end
