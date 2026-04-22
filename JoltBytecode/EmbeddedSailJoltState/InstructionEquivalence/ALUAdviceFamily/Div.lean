import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math

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

-- ----------------------------------------------------------------------------
-- Phase decomposition of `jolt_div`
-- ----------------------------------------------------------------------------
-- The 18 steps of `jolt_div` split cleanly into five phases, each one
-- ending at (or being dominated by) an assertion. The phase decomposition
-- lets the `jolt_div_concrete` proof close with 5 peels via `bind_run_of_ok`
-- instead of 17.
--
-- Phase postconditions (stored here as comments; proofs live below):
--   phase_setup:           v0=q, v1=|r|, div0-check passed
--   phase_overflow_check:  v2=adj_div, overflow-check assert passed
--   phase_quotient_product: q·v2 + r = a asserted
--   phase_remainder_bound: |r| < |v2| asserted
--   phase_writeback:       rd := v0 (=q)

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

/-- `jolt_div` as a composition of the five phases. Used to reshape the
bind chain before peeling. -/
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

/-- Bind-peel helper: if `m` runs to `.ok a js₁`, the whole chain
`(m >>= f).run js` reduces to `(f a).run js₁`. (Duplicated from
`toy.lean`; should eventually live in a shared `BindChain.lean`.) -/
theorem bind_run_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js₁ : SailJoltState} {a : α}
    (h : m.run js = .ok a js₁) :
    (m >>= f).run js = (f a).run js₁ := by
  show (m >>= f) js = (f a) js₁
  simp only [bind, EStateM.bind]
  rw [show m js = .ok a js₁ from h]

-- ----------------------------------------------------------------------------
-- Honest advice: the pure value functions that `execute_DIV` and
-- `execute_REM` write to `rd`, extracted directly from the transpiled
-- Sail bodies. These are the definitions of "honest quotient" and
-- "honest remainder" — not a re-implementation of RISC-V semantics, but
-- a re-statement of what the trusted side computes.
-- ----------------------------------------------------------------------------

/-- The pure 64-bit value `execute_DIV rs2 rs1 rd is_unsigned` writes to
`rd`, given the values read from `rs1` and `rs2`. Verbatim copy of the
`execute_DIV` body (minus the monadic read/write/return wrapper),
transcribed from `LeanRV64D/InstsEnd.lean:71105`. -/
def sail_div_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))) : Bool)
    then (Neg.neg (2 ^i (LeanRV64D.Functions.xlen -i 1))) else quotient
  to_bits_truncate (l := 64) quotient

/-- The pure 64-bit value `execute_REM rs2 rs1 rd is_unsigned` writes to
`rd`. Verbatim copy of the `execute_REM` body, transcribed from
`LeanRV64D/InstsEnd.lean:67637`. -/
def sail_rem_value (rs1_bits rs2_bits : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs1_bits) else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool) then (BitVec.toNatInt rs2_bits) else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  to_bits_truncate (l := 64) remainder

/-- Factoring lemma: `execute_DIV` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_div_value`, and a `pure RETIRE_SUCCESS`. Proof is
elided while we focus on statements. -/
theorem execute_DIV_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

theorem execute_REM_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  sorry

/-- Absolute value of a signed 64-bit bit-vector: `-x` when the MSB is
set, `x` otherwise. The oracle provides `|remainder|` rather than the
signed remainder, so the `rem_abs` advice is `bv_abs ∘ sail_rem_value`. -/
def bv_abs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

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
  -- PHASE 1 — advice loads + div0 check. Needs: honest advice pins `q`/`rem`
  -- so the div0 guard `divisor = 0 → q = -1` holds. Produces:
  --   v0 = q, v1 = rem, sail unchanged.
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_sail⟩ :
      ∃ js₁,
        (phase_setup rs2 q rem).run js = .ok RETIRE_SUCCESS js₁ ∧
        js₁.vregs 0 = q ∧
        js₁.vregs 1 = rem ∧
        js₁.sail = js.sail := by
    sorry
  -- PHASE 2 — adjusted divisor + MUL/MULH + overflow-check assert.
  -- Needs: h1_v0, h1_v1, h1_sail, hrs1, hrs2, and `v3_eq_v5_of_honest` to
  -- discharge the `assert_eq 3 5` guard. Produces:
  --   v0 = q (unchanged), v1 = rem (unchanged), v2 = adj, sail unchanged.
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_sail⟩ :
      ∃ js₂,
        (phase_overflow_check rs1 rs2).run js₁ = .ok RETIRE_SUCCESS js₂ ∧
        js₂.vregs 0 = q ∧
        js₂.vregs 1 = rem ∧
        js₂.vregs 2 = adj ∧
        js₂.sail = js.sail := by
    sorry
  -- PHASE 3 — signed-remainder reconstruction + `assert_eq_real v4 rs1`.
  -- Needs: h2_* invariants + hrs1 + the division relation
  -- `dividend = q·adj + signed_r` to discharge the guard. Produces:
  --   v0, v1, v2 unchanged, sail unchanged.
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :
      ∃ js₃,
        (phase_quotient_product rs1).run js₂ = .ok RETIRE_SUCCESS js₃ ∧
        js₃.vregs 0 = q ∧
        js₃.vregs 1 = rem ∧
        js₃.vregs 2 = adj ∧
        js₃.sail = js.sail := by
    sorry
  -- PHASE 4 — |adj| + `assert_valid_unsigned_remainder v1 v5`.
  -- Needs: h3_v1 (v1 = rem), h3_v2 (v2 = adj), and `rem.toNat < (bv_abs adj).toNat`
  -- to discharge the guard. Produces:
  --   v0 = q (unchanged), sail unchanged.
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :
      ∃ js₄,
        (phase_remainder_bound).run js₃ = .ok RETIRE_SUCCESS js₄ ∧
        js₄.vregs 0 = q ∧
        js₄.sail = js.sail := by
    sorry
  -- PHASE 5 — writeback `rd := v0`. Needs: h4_v0 (v0 = q), h4_sail.
  -- Produces final state with sail = stateAfterWrite js.sail rd q.
  obtain ⟨js₅, hrun5, h5_sail⟩ :
      ∃ js₅,
        (phase_writeback rd).run js₄ = .ok RETIRE_SUCCESS js₅ ∧
        js₅.sail = stateAfterWrite js.sail rd q := by
    sorry
  -- Stitch the five phase runs together via `bind_run_of_ok`.
  refine ⟨js₅, ?_, h5_sail⟩
  rw [jolt_div_phased]
  rw [bind_run_of_ok hrun1]
  rw [bind_run_of_ok hrun2]
  rw [bind_run_of_ok hrun3]
  rw [bind_run_of_ok hrun4]
  exact hrun5

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




end
