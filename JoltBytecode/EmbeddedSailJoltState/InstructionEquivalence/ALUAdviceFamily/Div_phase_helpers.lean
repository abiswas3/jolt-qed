import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_div`

The 18 steps of `jolt_div` split into five phases, each one ending at
(or dominated by) an assertion. This file holds:

* the **phase definitions** (pure monadic programs, each a 1–5 step
  sub-sequence of `jolt_div`),
* the **bind-peel helper** `bind_run_of_ok` used to chain phases
  together,
* the **phase-run lemmas** — one per phase — characterising what each
  phase produces given its preconditions and guards.

All phase-run lemmas are sorried for now; each will be discharged by
unfolding its phase into the raw bind chain and walking it with
`bind_run_of_ok`, using the per-primitive `_run`/`_run_ok` lemmas +
the supplied guard hypothesis.
-/

-- ----------------------------------------------------------------------------
-- Phase definitions
-- ----------------------------------------------------------------------------

/-- Phase 1 — advice loads + div-by-zero assert. -/
def phase_setup (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient
  let _ ← vreg_advice 1 rem_abs
  vreg_assert_valid_div0 rs2 0

/-- Phase 2 — adjusted divisor, MULH/MUL/SRAI, overflow-check assert. -/
def phase_overflow_check (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_change_divisor 2 rs1 rs2
  let _ ← vreg_MULH 3 0 2
  let _ ← vreg_MUL 4 0 2
  let _ ← vreg_SRAI 5 4 63
  vreg_assert_eq 3 5

/-- Phase 3 — reconstruct signed remainder, sum, assert equals dividend. -/
def phase_quotient_product (rs1 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI_from_real 3 rs1 63
  let _ ← vreg_XOR 5 1 3
  let _ ← vreg_SUB 5 5 3
  let _ ← vreg_ADD 4 4 5
  vreg_assert_eq_real 4 rs1

/-- Phase 4 — compute |adj_div|, assert |r| < |adj_div|. -/
def phase_remainder_bound : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI 3 2 63
  let _ ← vreg_XOR 5 2 3
  let _ ← vreg_SUB 5 5 3
  vreg_assert_valid_unsigned_remainder 1 5

/-- Phase 5 — move the quotient advice from v0 into real register rd. -/
def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_ADDI_to_real rd 0 0

-- ----------------------------------------------------------------------------
-- Bind-peel helper
-- ----------------------------------------------------------------------------

/-- Bind-peel: if `m` runs to `.ok a js₁`, the whole chain
`(m >>= f).run js` reduces to `(f a).run js₁`. -/
theorem bind_run_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js₁ : SailJoltState} {a : α}
    (h : m.run js = .ok a js₁) :
    (m >>= f).run js = (f a).run js₁ := by
  show (m >>= f) js = (f a) js₁
  simp only [bind, EStateM.bind]
  rw [show m js = .ok a js₁ from h]

/-- Bind-unpeel: if `(m >>= f).run js` ok-terminates, then there must
have been an intermediate `(a, js₁)` produced by `m`, and the tail
`f a` takes `js₁` to the same final state. Reverse direction of
`bind_run_of_ok`; the existential is forced because the intermediate
state is not visible in the compound hypothesis. Used by soundness-
style proofs that tear a chain apart from the outside in. -/
theorem bind_unpeel_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js' : SailJoltState} {b : β}
    (h : (m >>= f).run js = .ok b js') :
    ∃ (a : α) (js₁ : SailJoltState),
      m.run js = .ok a js₁ ∧ (f a).run js₁ = .ok b js' := by
  cases hmj : m.run js with
  | ok a js₁ =>
    refine ⟨a, js₁, rfl, ?_⟩
    have hpeel : (m >>= f).run js = (f a).run js₁ := bind_run_of_ok hmj
    rw [hpeel] at h
    exact h
  | error e js₁ =>
    exfalso
    have herr : (m >>= f).run js = .error e js₁ := by
      show (m >>= f) js = .error e js₁
      simp only [bind, EStateM.bind]
      rw [show m js = .error e js₁ from hmj]
    rw [herr] at h
    cases h

-- ----------------------------------------------------------------------------
-- Phase-run lemmas
-- ----------------------------------------------------------------------------

/-- Phase 1 — advice loads + div-by-zero assert. -/
theorem phase_setup_run
    (rs2 : regidx) (q rem : BitVec 64) (js : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (phase_setup rs2 q rem).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 2 — adjusted divisor + MUL/MULH + overflow-check assert.

The `hguard_overflow` hypothesis has the shape produced by
`v3_eq_v5_of_honest` (in `Div_math.lean`): `mulhs q adj = (q*adj).sshiftRight 63`. -/
theorem phase_overflow_check_run
    (rs1 rs2 : regidx)
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63) :
    ∃ js',
      (phase_overflow_check rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 4 = q * adj ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 3 — signed-remainder reconstruction + `assert_eq_real v4 rs1`.

`signed_rem` is `(rem XOR sign(dividend)) - sign(dividend)` — the
two's-complement sign-fixup of `|r|` to its signed form. The guard
`hguard_quotient_product` says `q*adj + signed_rem = dividend`, i.e.
the division equation reconstructs the dividend. -/
theorem phase_quotient_product_run
    (rs1 : regidx)
    (js : SailJoltState)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hguard_quotient_product :
        q * adj +
          (rem ^^^ dividend.sshiftRight 63 - dividend.sshiftRight 63)
        = dividend) :
    ∃ js',
      (phase_quotient_product rs1).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 4 — compute |adj| + `assert_valid_unsigned_remainder v1 v5`.

Guard: `rem.toNat < (|adj|).toNat` — the absolute remainder is strictly
less than the absolute adjusted divisor, unsigned. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hguard_rem_bound :
        rem.toNat <
          (adj ^^^ adj.sshiftRight 63 - adj.sshiftRight 63).toNat) :
    ∃ js',
      (phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  sorry

/-- Phase 5 — writeback `rd := v0`. Writes the quotient to real `rd`
via `liftSail (wX_bits rd q)`; produces `sail = stateAfterWrite js.sail rd q`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd q := by
  sorry

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction)
-- ----------------------------------------------------------------------------
-- Each of these takes `(phase_*.run js = .ok r js₁)` and extracts the
-- guard that the assert inside the phase enforced, plus the same state
-- invariants the forward version establishes. Used by `jolt_div_sound`.

/-- Phase 1 soundness — if `phase_setup` ok-terminates, the div0 guard
must have held and the advice landed in `v0`, `v1` without disturbing
`.sail`. -/
theorem phase_setup_run_sound
    (rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs2 q rem).run js = .ok r js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 2 soundness — if `phase_overflow_check` ok-terminates given
the standing invariants on `js`, the overflow-check assert's guard
held, and `v2`/`v4` now hold `adj`/`q·adj`. -/
theorem phase_overflow_check_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hp : (phase_overflow_check rs1 rs2).run js = .ok r js₁) :
    mulhs q adj = (q * adj).sshiftRight 63 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 4 = q * adj ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 3 soundness — if `phase_quotient_product` ok-terminates, the
division equation `q·adj + signed_rem = dividend` held. -/
theorem phase_quotient_product_run_sound
    (rs1 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hp : (phase_quotient_product rs1).run js = .ok r js₁) :
    q * adj +
      (rem ^^^ dividend.sshiftRight 63 - dividend.sshiftRight 63)
      = dividend ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 4 soundness — if `phase_remainder_bound` ok-terminates, the
unsigned remainder bound `rem.toNat < |adj|.toNat` held. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hp : (phase_remainder_bound).run js = .ok r js₁) :
    rem.toNat <
      (adj ^^^ adj.sshiftRight 63 - adj.sshiftRight 63).toNat ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  sorry

/-- Phase 5 soundness — writeback is unconditional; just characterises
the final state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd q := by
  sorry

end
