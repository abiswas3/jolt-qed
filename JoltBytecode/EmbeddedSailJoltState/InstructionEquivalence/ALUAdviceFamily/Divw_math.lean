import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `jolt_divw` (advice-verified DIVW)

The DIVW counterpart of `Div_math.lean`. Provides:

* The five **honest-advice guard lemmas** — `hguard_div0_of_honest_w`,
  `hguard_q_fits_of_honest_w`, `hguard_rem_nonneg_of_honest_w`,
  `hguard_quotient_product_of_honest_w`, `hguard_rem_bound_of_honest_w`
  — showing that each assertion's guard is satisfied when the oracle
  returns the honest values `(sail_divw_value, bv_abs sail_remw_value)`.
* A small Sail-side utility `rX_bits_x0_eq_zero` (reading register
  zero always yields `0#64`) used to discharge the `hx0` argument of
  `Divw.phase_rem_nonneg_run`.

All statements below are stated and **sorried**; they are the math
content needed to close `jolt_divw_concrete`. The DIVW soundness
analogues (uniqueness of `(q, rem)` from the four guards) live in a
separate uniqueness lemma, mirroring `advice_unique_of_guards` in
`Div_math.lean`.

Note: where DIV uses `shamt = 63` (sign bit of a 64-bit value), DIVW
uses `shamt = 31` (sign bit of a 32-bit value, sign-extended). The
moduli throughout shift accordingly.
-/

-- ----------------------------------------------------------------------------
-- Sail-side honest advice values
-- ----------------------------------------------------------------------------

/-- The pure 64-bit value `execute_DIVW rs2 rs1 rd is_unsigned` writes to
`rd`, given the values read from `rs1` and `rs2`. Verbatim copy of the
`execute_DIVW` body (minus the monadic read/write/return wrapper),
transcribed from `LeanRV64D/InstsEnd.lean:71082`. -/
def sail_divw_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_low) else (BitVec.toInt rs1_low)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_low) else (BitVec.toInt rs2_low)
  let quotient :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31)) else quotient
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-- 32-bit signed remainder corresponding to `sail_divw_value`. The
remainder advice supplied to `jolt_divw` is `bv_abs (sail_remw_value …)`,
matching the `quotient × divisor + remainder = dividend` identity at
32-bit width (sign-extended). -/
def sail_remw_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_low := Sail.BitVec.extractLsb rs1_bits 31 0
  let rs2_low := Sail.BitVec.extractLsb rs2_bits 31 0
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_low) else (BitVec.toInt rs1_low)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_low) else (BitVec.toInt rs2_low)
  let remainder :=
    if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)

-- The honest values, used by every guard lemma below.
section HonestValues
variable (dividend divisor : BitVec 64)

/-- Honest oracle quotient — the same value `execute_DIVW` writes to `rd`. -/
abbrev q_w  := sail_divw_value dividend divisor false
/-- Honest oracle `|remainder|`. -/
abbrev rem_w := bv_abs (sail_remw_value dividend divisor false)
/-- Sign-extended low 32 bits of `rs1` (the value carried in virtual `v6`). -/
abbrev sext_dividend_w :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
/-- Sign-extended low 32 bits of `rs2` (the value carried in virtual `v5`). -/
abbrev sext_divisor_w :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
/-- Adjusted divisor after the `(i32::MIN, -1)` overflow fix-up. -/
abbrev adj_w :=
  change_divisor_w_value (sext_dividend_w dividend) (sext_divisor_w divisor)

end HonestValues

-- ----------------------------------------------------------------------------
-- Sail-side utility: reading register x0 yields zero
-- ----------------------------------------------------------------------------

/-- Reading register zero from any Sail state returns `0#64` without
side effects. RV64 hardwires `x0 ≡ 0` per the ISA spec; the Sail
transpilation reflects this in `rX (Regno 0) = pure zero_reg`. Used
to discharge `Divw.phase_rem_nonneg_run`'s `hx0` argument. -/
theorem rX_bits_x0_eq_zero (s : SailState) :
    rX_bits (regidx.Regidx 0) s = .ok 0#64 s := by
  sorry

-- ----------------------------------------------------------------------------
-- The five honest-advice guard lemmas
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertValidDiv0` on the sign-extended divisor.**

When the *sign-extended* divisor `v5` is zero, the RISC-V DIVW spec
fixes the quotient as `-1` (32-bit, sign-extended to 64). Under honest
advice `q = sail_divw_value dividend divisor false`, the conjunction
`sext_divisor = 0 ∧ q ≠ -1` is impossible. -/
theorem hguard_div0_of_honest_w (dividend divisor : BitVec 64) :
    ¬ (sext_divisor_w divisor = 0#64 ∧
       q_w dividend divisor ≠ (-1 : BitVec 64)) := by
  sorry

/-- **Guard 2 — `VirtualAssertEQ v3 v0` (32-bit quotient round-trip).**

The quotient produced by Sail's `execute_DIVW` is the result of
`sign_extend ∘ to_bits_truncate 32` applied to a 32-bit integer,
hence it satisfies the round-trip identity
`sign_extend (extractLsb q 31 0) = q`. -/
theorem hguard_q_fits_of_honest_w (dividend divisor : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (q_w dividend divisor) 31 0)
      = q_w dividend divisor := by
  sorry

/-- **Guard 3 — `VirtualAssertEQ v4 x0` (`|rem|` ≥ 0 as i32).**

Honest `|rem|` is `(sail_remw_value … as i32).unsigned_abs`, which is
a `u32` zero-extended into 64 bits. Its high 33 bits are zero, so
arithmetic-shift-right by 31 yields `0#64`. -/
theorem hguard_rem_nonneg_of_honest_w (dividend divisor : BitVec 64) :
    shift_bits_right_arith (rem_w dividend divisor) (31 : BitVec 6) = 0#64 := by
  sorry

/-- **Guard 4 — `VirtualAssertEQ v3 v6` (32-bit division equation).**

`q · adj + signed_rem = sext(rs1)` at 32-bit width, where
`signed_rem = (rem XOR sign(sext_dividend)) - sign(sext_dividend)` is
the two's-complement sign-fixup of `|rem|`. The DIVW analogue of
`hguard_quotient_product_of_honest`, but with `shamt = 31` and the
sign-extended dividend in place of the real `rs1`. -/
theorem hguard_quotient_product_of_honest_w (dividend divisor : BitVec 64) :
    let q   := q_w dividend divisor
    let rem := rem_w dividend divisor
    let sd  := sext_dividend_w dividend
    let adj := adj_w dividend divisor
    q * adj +
      ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31)
      = sd := by
  sorry

/-- **Guard 5 — `VirtualAssertValidUnsignedRemainder`.**

Under honest advice, either the (sign-extended) adjusted divisor's
absolute value is zero, or `|rem|` is strictly less than `|adj|`
unsigned. The `XOR + SUB` with `shamt = 31` computes `|adj|` via
the two's-complement abs trick. -/
theorem hguard_rem_bound_of_honest_w (dividend divisor : BitVec 64) :
    let rem := rem_w dividend divisor
    let adj := adj_w dividend divisor
    ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat := by
  sorry

-- ----------------------------------------------------------------------------
-- Soundness uniqueness
-- ----------------------------------------------------------------------------

/-- **Soundness uniqueness.** If the five guards hold for some advice
`(q, rem)` and the sign-extension/adjustment relations are honestly
realised by `(sd, sv, adj)`, then `(q, rem)` is the unique honest
advice pair `(sail_divw_value, bv_abs sail_remw_value)`.

DIVW analogue of `advice_unique_of_guards` from `Div_math.lean`, but
with five guards (DIV has four — DIVW adds the `|rem|` ≥ 0 check). The
proof plan splits on `sv = 0`, the overflow pair `(i32::MIN, -1)`, and
the normal case (32-bit Int uniqueness routed through truncating
quotient/remainder, transported from `BitVec 64` to the 32-bit Int
domain using the round-trip identity from guard 2 to rule out
quotient overflow). -/
theorem advice_unique_of_guards_w
    (dividend divisor q rem adj : BitVec 64)
    (sd sv : BitVec 64)
    (hsd : sd = sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0))
    (hsv : sv = sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0))
    (hadj : adj = change_divisor_w_value sd sv)
    (h1 : ¬ (sv = 0#64 ∧ q ≠ (-1 : BitVec 64)))
    (h2 : sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q)
    (h3 : shift_bits_right_arith rem (31 : BitVec 6) = 0#64)
    (h4 : q * adj +
            ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31)
          = sd)
    (h5 : ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
            rem.toNat <
              ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat) :
    q = sail_divw_value dividend divisor false ∧
    rem = bv_abs (sail_remw_value dividend divisor false) := by
  sorry

end
