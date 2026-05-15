import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu_phase_helpers
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVU: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/divu.rs::inline_sequence`
(XLEN = 64). The Rust inline sequence contains 8 instructions; each
one appears below as a single step with the Rust mnemonic in the
trailing comment.

Virtual register allocation (Rust → Lean vreg index):
```
v0 = quotient                 (from oracle)
v1 = temporary                (q*divisor, then dividend - q*divisor)
```

Verification strategy (per Rust source):
1. `quotient` arrives as untrusted oracle advice.
2. `divisor = 0 ⇒ quotient = u64::MAX` (handled by `VirtualAssertValidDiv0`).
3. `quotient × divisor` does not overflow 64 bits unsigned.
4. `quotient × divisor ≤ dividend` (unsigned).
5. `remainder = dividend − quotient × divisor` and
   `divisor = 0 ∨ remainder < divisor` (unsigned).
-/

/-- The Jolt inline expansion of RISC-V `DIVU` at `XLEN = 64`. Takes the
oracle's advice (`quotient`) as an explicit parameter. Each line below is
one Jolt-ISA instruction, mirroring the `emit_X` calls in
`tracer/src/instruction/divu.rs::inline_sequence`. -/
def jolt_divu (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                              -- VirtualAdvice              v0, 0
  let _ ← vreg_assert_valid_div0 rs2 0                        -- VirtualAssertValidDiv0     rs2, v0, 0
  let _ ← vreg_assert_mulu_no_overflow 0 rs2                  -- VirtualAssertMulUNoOverflow v0, rs2, 0
  let _ ← vreg_MUL_from_real_vs2 1 0 rs2                      -- MUL                        v1, v0, rs2
  let _ ← vreg_assert_lte_real 1 rs1                          -- VirtualAssertLTE           v1, rs1, 0
  let _ ← vreg_SUB_from_real_vs1 1 rs1 1                      -- SUB                        v1, rs1, v1
  let _ ← vreg_assert_valid_unsigned_remainder_real 1 rs2     -- VirtualAssertValidUnsignedRemainder v1, rs2, 0
  vreg_ADDI_to_real rd 0 0                                    -- ADDI                       rd, v0, 0  (move quotient)

/-- `jolt_divu` as a composition of the five phases (defined in
`Divu_phase_helpers.lean`). Used to reshape the bind chain before
peeling. -/
theorem jolt_divu_phased (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) :
    jolt_divu rs2 rs1 rd quotient = (do
      let _ ← Divu.phase_setup rs2 quotient
      let _ ← Divu.phase_overflow_check rs2
      let _ ← Divu.phase_quotient_product rs1 rs2
      let _ ← Divu.phase_remainder_bound rs1 rs2
      Divu.phase_writeback rd) := by
  simp [jolt_divu, Divu.phase_setup, Divu.phase_overflow_check,
        Divu.phase_quotient_product, Divu.phase_remainder_bound,
        Divu.phase_writeback, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_divu` with honest advice from state
`js` succeeds (no assertion ever fires), and the resulting Sail state
is `js.sail` with register `rd` overwritten by
`sail_div_value dividend divisor true`. -/
theorem jolt_divu_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_divu rs2 rs1 rd
          (sail_div_value dividend divisor true)).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_div_value dividend divisor true) := by
  -- Local abbreviation for the honest quotient.
  let q := sail_div_value dividend divisor true
  -- Four honest-advice guards, each proved as a pure-math lemma in `Divu_math.lean`.
  have hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_u dividend divisor
  have hguard_no_overflow : q.toNat * divisor.toNat < 2^64 :=
    hguard_no_overflow_of_honest_u dividend divisor
  have hguard_lte : (q * divisor).toNat ≤ dividend.toNat :=
    hguard_q_times_d_le_dividend_of_honest_u dividend divisor
  have hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat :=
    hguard_rem_bound_of_honest_u dividend divisor
  -- PHASE 1 — advice + div0 check.
  obtain ⟨js₁, hrun1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run rs2 q js divisor hrs2 hguard_div0
  -- PHASE 2 — no-overflow check.
  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run rs2 js₁ q divisor hrs2_js1 h1_v0 hguard_no_overflow
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 — MUL + LTE.
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_js2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run rs1 rs2 js₂ q dividend divisor
      hrs1_js2 hrs2_js2 h2_v0 hguard_lte
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  -- PHASE 4 — SUB + remainder-bound.
  have hrs1_js3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_js3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    Divu.phase_remainder_bound_run rs1 rs2 js₃ q dividend divisor
      hrs1_js3 hrs2_js3 h3_v0 h3_v1 hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  -- PHASE 5 — writeback.
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divu.phase_writeback_run rd js₄ js.sail q h4_v0 h4_sail_orig
  -- Stitch the five phase runs together via `bind_run_of_ok`.
  refine ⟨js₅, ?_, h5_sail⟩
  rw [jolt_divu_phased]
  rw [bind_run_of_ok hrun1]
  rw [bind_run_of_ok hrun2]
  rw [bind_run_of_ok hrun3]
  rw [bind_run_of_ok hrun4]
  exact hrun5

/-- Factoring lemma: `execute_DIV` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_div_value`, and a `pure RETIRE_SUCCESS`. -/
theorem execute_DIVU_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

/-- **RHS reduction.** Running Sail's `execute_DIV ... is_unsigned = true`
on `js.sail` produces `.ok RETIRE_SUCCESS` with the final state equal to
`js.sail` with register `rd` overwritten by
`sail_div_value dividend divisor true`. -/
theorem execute_DIVU_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd true).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_div_value dividend divisor true)) := by
  rw [execute_DIVU_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** When the oracle's advice is exactly the unsigned
quotient `execute_DIV` would produce, Jolt's DIVU inline sequence
(a) never triggers an assertion failure and (b) leaves the Sail state
equal to running `execute_DIV ... is_unsigned = true` directly. -/
theorem jolt_divu_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_divu rs2 rs1 rd
                      (sail_div_value dividend divisor true)).run js) =
    (execute_DIV rs2 rs1 rd true).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_divu_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIVU_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** If `jolt_divu` runs to `.ok RETIRE_SUCCESS` on
*arbitrary* oracle advice `q`, then the advice must have been honest:
`q = sail_div_value dividend divisor true`.

Unlike DIV, DIVU's advice is the quotient alone — there is no remainder
advice, since the remainder is computed inline as `dividend − q * divisor`
and the assertions `q*divisor ≤ dividend` and `(dividend − q*divisor) <
divisor` together pin `q` down uniquely. -/
theorem jolt_divu_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_divu rs2 rs1 rd q).run js = .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor true := by
  -- Reshape: express the whole thing as five phases bound together.
  rw [jolt_divu_phased] at hok
  -- PHASE 1 unpeel + guard extraction.
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run_sound rs2 q js js₁ _ divisor hrs2 hp1
  -- PHASE 2 unpeel + guard extraction.
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run_sound rs2 js₁ js₂ _ q divisor hrs2_1 h1_v0 hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3 unpeel + guard extraction.
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨hguard3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run_sound rs1 rs2 js₂ js₃ _ q dividend divisor
      hrs1_2 hrs2_2 h2_v0 hp3
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  -- PHASE 4 unpeel + guard extraction.
  -- (Phase 5's writeback has no guard; we don't need to peel it.)
  obtain ⟨_, js₄, hp4, _⟩ := bind_unpeel_of_ok hok
  have hrs1_3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨hguard4, _, _⟩ :=
    Divu.phase_remainder_bound_run_sound rs1 rs2 js₃ js₄ _ q dividend divisor
      hrs1_3 hrs2_3 h3_v0 h3_v1 hp4
  -- All four guards now in hand. Uniqueness lemma closes the goal.
  exact advice_unique_of_guards_u dividend divisor q
    hguard1 hguard2 hguard3 hguard4

end
