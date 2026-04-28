import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Div_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_phase_helpers
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divw_math

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVW: Jolt inline sequence with oracle advice (RV64, signed 32-bit)

Transcribed from `tracer/src/instruction/divw.rs::inline_sequence`.
DIVW is an RV64 instruction that divides the lower 32 bits of `rs1` by
the lower 32 bits of `rs2` as signed integers, then sign-extends the
32-bit quotient to 64 bits and writes it to `rd`. The Rust inline
sequence contains 21 instructions; each appears below as a single step.

Virtual register allocation (Rust → Lean vreg index):
```
v0 = a2 = quotient            (from oracle)
v1 = a3 = |remainder|         (from oracle)
v2 = t0 = adjusted divisor    (after VirtualChangeDivisorW)
v3 = t1 = temporary
v4 = t2 = temporary
v5 = t3 = signed remainder / sign-extended divisor (reused)
v6 = t4 = sign-extended dividend
```

Verification strategy (per Rust source):
1. Sign-extend `rs1` and `rs2` to canonical 32-bit signed values in
   `t4` and `t3`.
2. Receive `quotient` and `|remainder|` as untrusted oracle advice.
3. `divisor = 0 ⇒ quotient = -1` (32-bit, sign-extended).
4. Adjust divisor to `1` on the `(i32::MIN, -1)` overflow pair.
5. Verify `quotient` fits in 32 bits via sign-extend round-trip.
6. Apply sign of dividend to `|remainder|` to recover the signed
   remainder; verify `dividend = quotient × divisor + remainder`.
7. Verify `|remainder| < |adjusted divisor|`.
8. Sign-extend the validated quotient into `rd`.
-/

/-- The Jolt inline expansion of RISC-V `DIVW` at `XLEN = 64`. Takes the
oracle's advice (`quotient`, `rem_abs`) as explicit parameters. Each
line below is one Jolt-ISA instruction, mirroring the `emit_X` calls in
`tracer/src/instruction/divw.rs::inline_sequence`. -/
def jolt_divw (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                          -- VirtualAdvice               v0, 0  (quotient)
  let _ ← vreg_advice 1 rem_abs                           -- VirtualAdvice               v1, 0  (|remainder|)
  let _ ← vreg_sign_extend_word_from_real 6 rs1           -- VirtualSignExtendWord       v6, rs1, 0
  let _ ← vreg_sign_extend_word_from_real 5 rs2           -- VirtualSignExtendWord       v5, rs2, 0
  let _ ← vreg_assert_valid_div0_v 5 0                    -- VirtualAssertValidDiv0      v5, v0, 0
  let _ ← vreg_change_divisor_w 2 6 5                     -- VirtualChangeDivisorW       v2, v6, v5
  let _ ← vreg_sign_extend_word 3 0                       -- VirtualSignExtendWord       v3, v0, 0
  let _ ← vreg_assert_eq 3 0                              -- VirtualAssertEQ             v3, v0, 0
  let _ ← vreg_SRAI 4 1 31                                -- SRAI                        v4, v1, 31
  let _ ← vreg_assert_eq_real 4 (regidx.Regidx 0)         -- VirtualAssertEQ             v4, x0, 0
  let _ ← vreg_SRAI 4 6 31                                -- SRAI                        v4, v6, 31
  let _ ← vreg_XOR 5 1 4                                  -- XOR                         v5, v1, v4
  let _ ← vreg_SUB 5 5 4                                  -- SUB                         v5, v5, v4
  let _ ← vreg_MUL 3 0 2                                  -- MUL                         v3, v0, v2
  let _ ← vreg_ADD 3 3 5                                  -- ADD                         v3, v3, v5
  let _ ← vreg_assert_eq 3 6                              -- VirtualAssertEQ             v3, v6, 0
  let _ ← vreg_SRAI 4 2 31                                -- SRAI                        v4, v2, 31
  let _ ← vreg_XOR 3 2 4                                  -- XOR                         v3, v2, v4
  let _ ← vreg_SUB 3 3 4                                  -- SUB                         v3, v3, v4
  let _ ← vreg_assert_valid_unsigned_remainder 1 3        -- VirtualAssertValidUnsignedRemainder v1, v3, 0
  vreg_sign_extend_word_to_real rd 0                      -- VirtualSignExtendWord       rd, v0, 0

/-- `jolt_divw` as a composition of the six phases (defined in
`Divw_phase_helpers.lean`). Used to reshape the bind chain before
peeling. -/
theorem jolt_divw_phased (rs2 rs1 rd : regidx)
    (quotient rem_abs : BitVec 64) :
    jolt_divw rs2 rs1 rd quotient rem_abs = (do
      let _ ← Divw.phase_setup rs1 rs2 quotient rem_abs
      let _ ← Divw.phase_overflow_check
      let _ ← Divw.phase_rem_nonneg
      let _ ← Divw.phase_quotient_product
      let _ ← Divw.phase_remainder_bound
      Divw.phase_writeback rd) := by
  simp [jolt_divw, Divw.phase_setup, Divw.phase_overflow_check,
        Divw.phase_rem_nonneg, Divw.phase_quotient_product,
        Divw.phase_remainder_bound, Divw.phase_writeback, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_divw` with honest advice from state
`js` succeeds (no assertion ever fires), and the resulting Sail state
is `js.sail` with register `rd` overwritten by
`sail_divw_value dividend divisor false`. -/
theorem jolt_divw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_divw rs2 rs1 rd
          (sail_divw_value dividend divisor false)
          (bv_abs (sail_remw_value dividend divisor false))).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_divw_value dividend divisor false) := by
  -- Local abbreviations for the honest advice values, sign-extended
  -- operands, and adjusted divisor.
  let q   := sail_divw_value dividend divisor false
  let rem := bv_abs (sail_remw_value dividend divisor false)
  let sd  := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sv  := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adj := change_divisor_w_value sd sv
  -- Five honest-advice guards, each proved as a pure-math lemma in
  -- `Divw_math.lean`.
  have hguard_div0 : ¬ (sv = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_w dividend divisor
  have hguard_q_fits : sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) = q :=
    hguard_q_fits_of_honest_w dividend divisor
  have hguard_rem_nonneg : shift_bits_right_arith rem (31 : BitVec 6) = 0#64 :=
    hguard_rem_nonneg_of_honest_w dividend divisor
  have hguard_quotient_product :
      q * adj + ((rem ^^^ sd.sshiftRight 31) - sd.sshiftRight 31) = sd :=
    hguard_quotient_product_of_honest_w dividend divisor
  have hguard_rem_bound :
      ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31) = 0#64 ∨
        rem.toNat < ((adj ^^^ adj.sshiftRight 31) - adj.sshiftRight 31).toNat :=
    hguard_rem_bound_of_honest_w dividend divisor
  -- PHASE 1 — advice loads + sign-extension prologue + div0 check.
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Divw.phase_setup_run rs1 rs2 q rem js dividend divisor hrs1 hrs2 hguard_div0
  -- PHASE 2 — adjusted divisor + 32-bit-quotient-fits check.
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Divw.phase_overflow_check_run js₁ q rem adj sd sv
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hguard_q_fits
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 — `|rem|` ≥ 0 (as i32) check. Needs `rX_bits x0 = 0`,
  -- transported across the running `.sail` chain.
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_v5, h3_v6, h3_sail⟩ :=
    Divw.phase_rem_nonneg_run js₂ q rem adj sd sv
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hguard_rem_nonneg
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  -- PHASE 4 — division-equation reconstruction.
  obtain ⟨js₄, hrun4, h4_v0, h4_v1, h4_v2, h4_sail⟩ :=
    Divw.phase_quotient_product_run js₃ q rem adj sd sv
      h3_v0 h3_v1 h3_v2 h3_v6 hguard_quotient_product
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  -- PHASE 5 — `|rem| < |adj|` bound.
  obtain ⟨js₅, hrun5, h5_v0, h5_sail⟩ :=
    Divw.phase_remainder_bound_run js₄ q rem adj h4_v0 h4_v1 h4_v2 hguard_rem_bound
  have h5_sail_orig : js₅.sail = js.sail := h5_sail.trans h4_sail_orig
  -- PHASE 6 — sign-extend writeback.  The honest-advice quotient is
  -- already sign-extended (round-trip identity `hguard_q_fits`), so the
  -- writeback's `sign_extend (extractLsb q 31 0)` collapses to `q` —
  -- which equals `sail_divw_value dividend divisor false` by definition.
  obtain ⟨js₆, hrun6, h6_sail⟩ :=
    Divw.phase_writeback_run rd js₅ js.sail q h5_v0 h5_sail_orig
  -- Stitch the six phase runs together via `bind_run_of_ok`.
  refine ⟨js₆, ?_, ?_⟩
  · rw [jolt_divw_phased]
    rw [bind_run_of_ok hrun1]
    rw [bind_run_of_ok hrun2]
    rw [bind_run_of_ok hrun3]
    rw [bind_run_of_ok hrun4]
    rw [bind_run_of_ok hrun5]
    exact hrun6
  · rw [h6_sail, hguard_q_fits]

/-- Factoring lemma: `execute_DIVW` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_divw_value`, and a `pure RETIRE_SUCCESS`. -/
theorem execute_DIVW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

/-- **RHS reduction.** Running Sail's `execute_DIVW ... is_unsigned = false`
on `js.sail` produces `.ok RETIRE_SUCCESS` with the final state equal to
`js.sail` with register `rd` overwritten by
`sail_divw_value dividend divisor false`. -/
theorem execute_DIVW_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd false).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_divw_value dividend divisor false)) := by
  rw [execute_DIVW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** When the oracle's advice is exactly the signed
32-bit quotient and `|remainder|` `execute_DIVW` would produce, Jolt's
DIVW inline sequence (a) never triggers an assertion failure and
(b) leaves the Sail state equal to running `execute_DIVW ... false`
directly. -/
theorem jolt_divw_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_divw rs2 rs1 rd
                      (sail_divw_value dividend divisor false)
                      (bv_abs (sail_remw_value dividend divisor false))).run js) =
    (execute_DIVW rs2 rs1 rd false).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_divw_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIVW_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** If `jolt_divw` runs to `.ok RETIRE_SUCCESS` on
*arbitrary* oracle advice `(q, rem)`, then the advice must have been
honest: `q` is exactly `sail_divw_value …` and `rem` is exactly
`bv_abs (sail_remw_value …)`. -/
theorem jolt_divw_sound (rs2 rs1 rd : regidx)
    (q rem : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_divw rs2 rs1 rd q rem).run js = .ok RETIRE_SUCCESS js') :
    q = sail_divw_value dividend divisor false ∧
    rem = bv_abs (sail_remw_value dividend divisor false) := by
  -- Reshape: express the whole thing as six phases bound together.
  rw [jolt_divw_phased] at hok
  -- Local abbreviations for the sign-extended operands and adjusted divisor.
  let sd  := sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let sv  := sign_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let adj := change_divisor_w_value sd sv
  -- PHASE 1 unpeel + guard extraction.
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_v5, h1_v6, h1_sail⟩ :=
    Divw.phase_setup_run_sound rs1 rs2 q rem js js₁ _ dividend divisor
      hrs1 hrs2 hp1
  -- PHASE 2 unpeel + guard extraction.
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v5, h2_v6, h2_sail⟩ :=
    Divw.phase_overflow_check_run_sound js₁ js₂ _ q rem adj sd sv
      h1_v0 h1_v1 h1_v5 h1_v6 rfl hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 unpeel + guard extraction.
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  have hx0_js2 : rX_bits (regidx.Regidx 0) js₂.sail = .ok 0#64 js₂.sail :=
    h2_sail_orig.symm ▸ rX_bits_x0_eq_zero js.sail
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, _, h3_v6, _⟩ :=
    Divw.phase_rem_nonneg_run_sound js₂ js₃ _ q rem adj sd sv
      h2_v0 h2_v1 h2_v2 h2_v5 h2_v6 hx0_js2 hp3
  -- PHASE 4 unpeel + guard extraction.
  obtain ⟨_, js₄, hp4, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard4, h4_v0, h4_v1, h4_v2, _⟩ :=
    Divw.phase_quotient_product_run_sound js₃ js₄ _ q rem adj sd sv
      h3_v0 h3_v1 h3_v2 h3_v6 hp4
  -- PHASE 5 unpeel + guard extraction.
  -- (Phase 6's writeback has no guard; we don't need to peel it.)
  obtain ⟨_, js₅, hp5, _⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard5, _, _⟩ :=
    Divw.phase_remainder_bound_run_sound js₄ js₅ _ q rem adj
      h4_v0 h4_v1 h4_v2 hp5
  -- All five guards now in hand. Uniqueness lemma closes the goal.
  exact advice_unique_of_guards_w dividend divisor q rem adj sd sv
    rfl rfl rfl hguard1 hguard2 hguard3 hguard4 hguard5

end
