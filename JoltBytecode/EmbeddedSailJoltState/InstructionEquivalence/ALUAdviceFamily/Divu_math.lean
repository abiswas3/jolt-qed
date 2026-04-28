import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divu_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `jolt_divu` (advice-verified DIVU)

The DIVU counterpart of `Div_math.lean`. Provides:

* The four **honest-advice guard lemmas** —
  `hguard_div0_of_honest_u`, `hguard_no_overflow_of_honest_u`,
  `hguard_q_times_d_le_dividend_of_honest_u`,
  `hguard_rem_bound_of_honest_u` — showing that each assertion's
  guard is satisfied when the oracle returns the honest quotient
  `sail_div_value dividend divisor true`.
* The **uniqueness lemma** `advice_unique_of_guards_u` — used by
  soundness to pin the advice down to the honest value.

DIVU has 4 guards (DIV had 4, DIVW had 5). It needs no `_of_honest`
analogue for `q`-fits-in-32 / `|rem|`-non-neg / signed-rem
reconstruction since DIVU is unsigned-only.

`sail_div_value … true` (with `is_unsigned = true`) is reused from
`Div_math.lean` rather than restated — it's the same Sail function.

All statements below are stated and **sorried**.
-/

-- ----------------------------------------------------------------------------
-- The four honest-advice guard lemmas
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertValidDiv0`.**

When the divisor is zero, RV64M DIVU specifies `quotient = u64::MAX`
(i.e. `-1` as a `BitVec 64`). Sail's `execute_DIV ... is_unsigned = true`
implements this in the first branch of `sail_div_value`: if
`rs2_int = 0` it returns `-1`. So under honest advice the conjunction
`divisor = 0 ∧ q ≠ -1` is impossible. -/
theorem hguard_div0_of_honest_u (dividend divisor : BitVec 64) :
    ¬ (divisor = 0#64 ∧
       sail_div_value dividend divisor true ≠ (-1 : BitVec 64)) := by
  sorry

/-- **Guard 2 — `VirtualAssertMulUNoOverflow`.**

Under honest advice, `q × divisor` does not overflow 64 bits unsigned.
For non-zero divisor `q = ⌊dividend / divisor⌋`, so
`q * divisor ≤ dividend < 2^64`. For zero divisor `q = -1 = u64::MAX`
and the product wraps to `0` — but Sail's `sail_div_value` returns
`-1` directly, so `q.toNat * divisor.toNat = (2^64 - 1) * 0 = 0 < 2^64`. -/
theorem hguard_no_overflow_of_honest_u (dividend divisor : BitVec 64) :
    (sail_div_value dividend divisor true).toNat * divisor.toNat < 2^64 := by
  sorry

/-- **Guard 3 — `VirtualAssertLTE` (`q × divisor ≤ dividend`).**

The unsigned division identity: for non-zero divisor,
`q = ⌊dividend / divisor⌋` satisfies `q · divisor ≤ dividend`. For
zero divisor, `q = u64::MAX` but `q × 0 = 0 ≤ dividend` trivially. -/
theorem hguard_q_times_d_le_dividend_of_honest_u (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor true
    (q * divisor).toNat ≤ dividend.toNat := by
  sorry

/-- **Guard 4 — `VirtualAssertValidUnsignedRemainder`.**

The unsigned remainder `dividend − q*divisor` is strictly less than
the divisor — the standard division identity. The Rust short-circuit
on `divisor = 0` is captured by the left disjunct. -/
theorem hguard_rem_bound_of_honest_u (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor true
    divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat := by
  sorry

-- ----------------------------------------------------------------------------
-- Soundness uniqueness
-- ----------------------------------------------------------------------------

/-- **Soundness uniqueness.** If the four guards hold for some advice
`q`, then `q` is the unique honest value `sail_div_value dividend
divisor true`.

DIVU analogue of `advice_unique_of_guards` from `Div_math.lean`, but
with four unsigned guards (DIV's signed product needs `mulhs`-equation,
DIVU's unsigned product needs no-overflow). The proof plan splits on
`divisor = 0` (forces `q = -1` from guard 1) and the normal case
(unsigned uniqueness of truncating quotient with `0 ≤ rem < divisor`,
where `rem := dividend − q × divisor`). -/
theorem advice_unique_of_guards_u
    (dividend divisor q : BitVec 64)
    (h1 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)))
    (h2 : q.toNat * divisor.toNat < 2^64)
    (h3 : (q * divisor).toNat ≤ dividend.toNat)
    (h4 : divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    q = sail_div_value dividend divisor true := by
  sorry

end
