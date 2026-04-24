import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIV: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/div.rs::inline_sequence`
(XLEN = 64, so `shmat = 63`). The Rust inline sequence contains 18
instructions; each one appears below as a single step with the Rust
mnemonic in the trailing comment.

Virtual register allocation:
```
v0 = a2 = quotient             (from oracle)
v1 = a3 = |remainder|          (from oracle)
v2 = t0 = adjusted divisor
v3 = t1 = temporary
v4 = t2 = temporary
v5 = t3 = temporary
```

The proof structure for DIV will differ from the rest of the ALU family
because correctness relies on (a) oracle advice, (b) constraint
assertions (`VirtualAssertEQ`, `VirtualAssertValidDiv0`,
`VirtualAssertValidUnsignedRemainder`), and (c) special-case handling
for division by zero and signed overflow. The virtual-assert and
change-divisor primitives are stubbed below; their semantics will be
pinned down when the DIV proof is written.
-/

-- ----------------------------------------------------------------------------
-- Jolt DIV inline sequence
-- ----------------------------------------------------------------------------
-- The generic Jolt-ISA primitives used below (`vreg_advice`,
-- `vreg_assert_eq`, `vreg_assert_eq_real`) live in
-- `VirtualInstructions.lean`. The DIV/REM-family-specific constraint
-- primitives (`vreg_change_divisor`, `vreg_assert_valid_div0`,
-- `vreg_assert_valid_unsigned_remainder`) live in `Primitives.lean`
-- alongside this file.

/-- The Jolt inline expansion of RISC-V `DIV` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. Each
line below is one Jolt-ISA instruction, mirroring the `emit_X` calls in
`tracer/src/instruction/div.rs::inline_sequence`. -/
def jolt_div (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                      -- VirtualAdvice v0, 0    (quotient)
  let _ ← vreg_advice 1 rem_abs                       -- VirtualAdvice v1, 0    (|remainder|)
  let _ ← vreg_assert_valid_div0 rs2 0                -- VirtualAssertValidDiv0 rs2, v0, 0
  let _ ← vreg_change_divisor 2 rs1 rs2               -- VirtualChangeDivisor   v2, rs1, rs2
  let _ ← vreg_MULH 3 0 2                             -- MULH                   v3, v0, v2
  let _ ← vreg_MUL 4 0 2                              -- MUL                    v4, v0, v2
  let _ ← vreg_SRAI 5 4 63                            -- SRAI                   v5, v4, 63
  let _ ← vreg_assert_eq 3 5                          -- VirtualAssertEQ        v3, v5, 0
  let _ ← vreg_SRAI_from_real 3 rs1 63                -- SRAI                   v3, rs1, 63
  let _ ← vreg_XOR 5 1 3                              -- XOR                    v5, v1, v3
  let _ ← vreg_SUB 5 5 3                              -- SUB                    v5, v5, v3
  let _ ← vreg_ADD 4 4 5                              -- ADD                    v4, v4, v5
  let _ ← vreg_assert_eq_real 4 rs1                   -- VirtualAssertEQ        v4, rs1, 0
  let _ ← vreg_SRAI 3 2 63                            -- SRAI                   v3, v2, 63
  let _ ← vreg_XOR 5 2 3                              -- XOR                    v5, v2, v3
  let _ ← vreg_SUB 5 5 3                              -- SUB                    v5, v5, v3
  let _ ← vreg_assert_valid_unsigned_remainder 1 5    -- VirtualAssertValidUnsignedRemainder v1, v5, 0
  vreg_ADDI_to_real rd 0 0                            -- ADDI                   rd, v0, 0   (move quotient)

/-- `jolt_div` as a composition of the five phases (defined in
`Div_phase_helpers.lean`). Used to reshape the bind chain before
peeling. -/
theorem jolt_div_phased (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) :
    jolt_div rs2 rs1 rd quotient rem_abs = (do
      let _ ← phase_setup rs2 quotient rem_abs
      let _ ← phase_overflow_check rs1 rs2
      let _ ← phase_quotient_product rs1
      let _ ← phase_remainder_bound
      phase_writeback rd) := by
  simp [jolt_div, phase_setup, phase_overflow_check, phase_quotient_product,
        phase_remainder_bound, phase_writeback, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_div` with honest advice from state
`js` succeeds (no assertion ever fires), and the resulting Sail state
is `js.sail` with register `rd` overwritten by `sail_div_value dividend
divisor false`.

This is the Jolt-side "what happens when we run the whole 18-step
sequence" characterisation. The proof body walks the bind chain with
`bind_run_of_ok`, one `_run`/`_run_ok` lemma per step, discharging each
assert's guard from the honest-advice hypotheses (via pure lemmas such
as `v3_eq_v5_of_honest`). -/
theorem jolt_div_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_div rs2 rs1 rd
          (sail_div_value dividend divisor false)
          (bv_abs (sail_rem_value dividend divisor false))).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_div_value dividend divisor false) := by
  -- Local abbreviations for the honest advice values and adjusted divisor.
  let q   := sail_div_value dividend divisor false
  let rem := bv_abs (sail_rem_value dividend divisor false)
  let adj := change_divisor_value dividend divisor
  -- Guards derived from honest advice; each proved as a pure-math lemma
  -- in `Div_math.lean`.
  have hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest dividend divisor
  have hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63 :=
    hguard_overflow_of_honest dividend divisor
  have hguard_quotient_product :
      q * adj +
        (rem ^^^ dividend.sshiftRight 63 - dividend.sshiftRight 63) = dividend :=
    hguard_quotient_product_of_honest dividend divisor
  have hguard_rem_bound :
      rem.toNat < (adj ^^^ adj.sshiftRight 63 - adj.sshiftRight 63).toNat :=
    hguard_rem_bound_of_honest dividend divisor
  -- PHASE 1 — advice loads + div0 check.
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_sail⟩ :=
    phase_setup_run rs2 q rem js divisor hrs2 hguard_div0
  -- PHASE 2 — transport the rs1/rs2 reads across js₁.sail = js.sail.
  have hrs1_js1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v4, h2_sail⟩ :=
    phase_overflow_check_run rs1 rs2 js₁ q rem adj dividend divisor
      hrs1_js1 hrs2_js1 h1_v0 h1_v1 rfl hguard_overflow
  -- Chain the sail equalities for use downstream.
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 — signed-remainder reconstruction + assert_eq_real v4 rs1.
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    phase_quotient_product_run rs1 js₂ q rem adj dividend
      hrs1_js2 h2_v0 h2_v1 h2_v2 h2_v4 hguard_quotient_product
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  -- PHASE 4 — |adj| + assert_valid_unsigned_remainder.
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    phase_remainder_bound_run js₃ q rem adj h3_v0 h3_v1 h3_v2 hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  -- PHASE 5 — writeback.
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    phase_writeback_run rd js₄ js.sail q h4_v0 h4_sail_orig
  -- Stitch the five phase runs together via `bind_run_of_ok`.
  refine ⟨js₅, ?_, h5_sail⟩
  rw [jolt_div_phased]
  rw [bind_run_of_ok hrun1]
  rw [bind_run_of_ok hrun2]
  rw [bind_run_of_ok hrun3]
  rw [bind_run_of_ok hrun4]
  exact hrun5

/-- Factoring lemma: `execute_DIV` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_div_value`, and a `pure RETIRE_SUCCESS`. -/
theorem execute_DIV_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

/-- **RHS reduction.** Running Sail's `execute_DIV` on `js.sail` produces
`.ok RETIRE_SUCCESS` with the final state equal to `js.sail` with
register `rd` overwritten by `sail_div_value dividend divisor false`.

Single-step Sail reduction — proved by `execute_DIV_factored` +
monadic plumbing, no bind-chain walk needed. -/
theorem execute_DIV_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd false).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_div_value dividend divisor false)) := by
  rw [execute_DIV_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor false) js.sail
  rw [hw]
  simp only []     -- iota: collapse `match .ok () s' with | …`
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** When the oracle's advice is exactly what
`execute_DIV` and `execute_REM` would produce for the current register
values, Jolt's DIV inline sequence (a) never triggers an assertion
failure and (b) leaves the Sail state equal to running `execute_DIV`
directly.

Proved by rewriting both sides with `jolt_div_concrete` and
`execute_DIV_reduces`; they produce matching `stateAfterWrite`
expressions, then `projectResult` collapses. -/
theorem jolt_div_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_div rs2 rs1 rd
                      (sail_div_value dividend divisor false)
                      (bv_abs (sail_rem_value dividend divisor false))).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail := by
  -- LHS — run jolt_div; get the final Jolt state js' and its .sail form.
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_div_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  -- RHS — reduce execute_DIV to the matching `.ok RETIRE_SUCCESS (stateAfterWrite …)`.
  rw [execute_DIV_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** If `jolt_div` runs to `.ok RETIRE_SUCCESS` on *arbitrary*
oracle advice `(q, rem)`, then the advice must have been honest: `q` is
exactly `sail_div_value …` and `rem` is exactly `bv_abs (sail_rem_value …)`.

Contrapositive form of "bad advice ⇒ some assert fires". Proved by
extracting the four assertion guards from the successful run and feeding
them into a pure uniqueness lemma (to be stated in `Div_math.lean`):
the conjunction of the four guards pins `(q, rem)` down uniquely as the
honest pair. -/
theorem jolt_div_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_div rs2 rs1 rd q rem).run js = .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor false ∧
    rem = bv_abs (sail_rem_value dividend divisor false) := by
  -- Reshape: express the whole thing as five phases bound together.
  rw [jolt_div_phased] at hok
  -- Local abbreviation for the adjusted divisor (needed to invoke the
  -- guard-extracting phase lemmas, all of which speak in terms of `adj`).
  let adj := change_divisor_value dividend divisor
  -- PHASE 1 unpeel + guard extraction.
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_sail⟩ :=
    phase_setup_run_sound rs2 q rem js js₁ _ divisor hrs2 hp1
  -- PHASE 2 unpeel + guard extraction.
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_1 : rX_bits rs1 js₁.sail = .ok dividend js₁.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v4, h2_sail⟩ :=
    phase_overflow_check_run_sound rs1 rs2 js₁ js₂ _ q rem adj dividend divisor
      hrs1_1 hrs2_1 h1_v0 h1_v1 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 unpeel + guard extraction.
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, _⟩ :=
    phase_quotient_product_run_sound rs1 js₂ js₃ _ q rem adj dividend
      hrs1_2 h2_v0 h2_v1 h2_v2 h2_v4 hp3
  -- PHASE 4 unpeel + guard extraction.
  -- (Phase 5's writeback has no guard; we don't need to peel it.)
  obtain ⟨_, js₄, hp4, _⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard4, _, _⟩ :=
    phase_remainder_bound_run_sound js₃ js₄ _ q rem adj
      h3_v0 h3_v1 h3_v2 hp4
  -- All four guards now in hand. Uniqueness lemma closes the goal.
  exact advice_unique_of_guards dividend divisor q rem adj rfl
    hguard1 hguard2 hguard3 hguard4

end
