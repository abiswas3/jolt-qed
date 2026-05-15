import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_phase_helpers
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVUW: Jolt inline sequence with oracle advice (RV64, unsigned 32-bit)

Transcribed from `tracer/src/instruction/divuw.rs::inline_sequence`.
DIVUW is an RV64 instruction that divides the lower 32 bits of `rs1`
by the lower 32 bits of `rs2` as **unsigned** integers, then
sign-extends the 32-bit quotient to 64 bits and writes it to `rd`.
The Rust inline sequence contains 11 instructions.

Virtual register allocation (Rust → Lean vreg index):
```
v0 = rs1 = zero-extended dividend (low 32 bits of real rs1)
v1 = rs2 = zero-extended divisor  (low 32 bits of real rs2)
v2 = quo = quotient               (from oracle, u32 zero-extended)
v3 = temp = q × divisor / remainder / sign-extended quotient (reused)
```

Verification strategy (per Rust source):
1. Zero-extend `rs1` and `rs2` to canonical u32 in `v0`/`v1`.
2. Receive `quotient` as oracle advice in `v2`.
3. `q × divisor` does not overflow 64 bits unsigned.
4. `q × divisor ≤ dividend` (unsigned).
5. `dividend − q × divisor < divisor` (or `divisor = 0`) — the
   remainder identity, computed inline by SUB.
6. After sign-extending `q` to 64 bits in `v3`, assert div-by-zero
   case: `divisor = 0 ⇒ sext(q) = -1` (i.e., `q = u32::MAX`).
7. Move sign-extended quotient to `rd`.
-/

/-- The Jolt inline expansion of RISC-V `DIVUW` at `XLEN = 64`. Takes the
oracle's advice (`quotient` as u32 zero-extended to u64) as an explicit
parameter. -/
def jolt_divuw (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_zero_extend_word_from_real 0 rs1            -- VirtualZeroExtendWord  v0, rs1, 0
  let _ ← vreg_zero_extend_word_from_real 1 rs2            -- VirtualZeroExtendWord  v1, rs2, 0
  let _ ← vreg_advice 2 quotient                           -- VirtualAdvice          v2, 0
  let _ ← vreg_assert_mulu_no_overflow_v 2 1               -- VirtualAssertMulUNoOverflow v2, v1, 0
  let _ ← vreg_MUL 3 2 1                                   -- MUL                    v3, v2, v1
  let _ ← vreg_assert_lte 3 0                              -- VirtualAssertLTE       v3, v0, 0
  let _ ← vreg_SUB 3 0 3                                   -- SUB                    v3, v0, v3
  let _ ← vreg_assert_valid_unsigned_remainder 3 1         -- VirtualAssertValidUnsignedRemainder v3, v1, 0
  let _ ← vreg_sign_extend_word 3 2                        -- VirtualSignExtendWord  v3, v2, 0
  let _ ← vreg_assert_valid_div0_v 1 3                     -- VirtualAssertValidDiv0 v1, v3, 0
  vreg_ADDI_to_real rd 3 0                                 -- ADDI                   rd, v3, 0

/-- `jolt_divuw` as a composition of the five phases (defined in
`Divuw_phase_helpers.lean`). -/
theorem jolt_divuw_phased (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) :
    jolt_divuw rs2 rs1 rd quotient = (do
      let _ ← Divuw.phase_setup rs1 rs2 quotient
      let _ ← Divuw.phase_quotient_product
      let _ ← Divuw.phase_remainder_bound
      let _ ← Divuw.phase_div0_check
      Divuw.phase_writeback rd) := by
  simp [jolt_divuw, Divuw.phase_setup, Divuw.phase_quotient_product,
        Divuw.phase_remainder_bound, Divuw.phase_div0_check,
        Divuw.phase_writeback, bind_assoc]

-- ----------------------------------------------------------------------------
-- Completeness
-- ----------------------------------------------------------------------------

/-- **LHS reduction.** Running `jolt_divuw` with honest advice from
state `js` succeeds and the resulting Sail state is `js.sail` with `rd`
overwritten by `sail_divw_value dividend divisor true`. -/
theorem jolt_divuw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_divuw rs2 rs1 rd
          (sail_divuw_advice dividend divisor)).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_divw_value dividend divisor true) := by
  -- Local abbreviations.
  let q  := sail_divuw_advice dividend divisor
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  -- Four honest-advice guards.
  have hguard_no_overflow : q.toNat * zv.toNat < 2^64 :=
    hguard_no_overflow_of_honest_uw dividend divisor
  have hguard_lte : (q * zv).toNat ≤ zd.toNat :=
    hguard_q_times_d_le_dividend_of_honest_uw dividend divisor
  have hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat :=
    hguard_rem_bound_of_honest_uw dividend divisor
  have hguard_div0 :
      ¬ (zv = 0#64 ∧
         sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_uw dividend divisor
  -- Sign-extend identity for q (round-trip on the u32 advice).
  have h_sext_q :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value dividend divisor
  -- PHASE 1.
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run rs1 rs2 q js dividend divisor hrs1 hrs2 hguard_no_overflow
  -- PHASE 2.
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run js₁ q zd zv h1_v0 h1_v1 h1_v2 hguard_lte
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  -- PHASE 3.
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run js₂ q zd zv h2_v0 h2_v1 h2_v2 h2_v3 hguard_rem_bound
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  -- PHASE 4.
  obtain ⟨js₄, hrun4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run js₃ q zv h3_v1 h3_v2 hguard_div0
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  -- PHASE 5 — writeback writes v3 (= sext_q) to rd.
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divuw.phase_writeback_run rd js₄ js.sail
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig
  -- Stitch + rewrite the writeback's stateAfterWrite to use sail_divw_value.
  refine ⟨js₅, ?_, ?_⟩
  · rw [jolt_divuw_phased]
    rw [bind_run_of_ok hrun1, bind_run_of_ok hrun2, bind_run_of_ok hrun3,
        bind_run_of_ok hrun4]
    exact hrun5
  · rw [h5_sail, h_sext_q]

/-- Factoring lemma: `execute_DIVW` collapses to one `rX_bits` per source,
one `wX_bits` of `sail_divw_value`, and a `pure RETIRE_SUCCESS`. -/
theorem execute_DIVUW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

/-- **RHS reduction.** Sail's `execute_DIVW ... is_unsigned = true` —
the same Sail entry as DIVW, just with the unsigned bool flipped. -/
theorem execute_DIVUW_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd true).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_divw_value dividend divisor true)) := by
  rw [execute_DIVUW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- **Completeness.** `jolt_divuw` with honest advice matches Sail's
`execute_DIVW ... true`. -/
theorem jolt_divuw_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_divuw rs2 rs1 rd
                      (sail_divuw_advice dividend divisor)).run js) =
    (execute_DIVW rs2 rs1 rd true).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_divuw_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_DIVUW_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

-- ----------------------------------------------------------------------------
-- Soundness
-- ----------------------------------------------------------------------------

/-- **Soundness.** Any successful run of `jolt_divuw` on advice `q`
produces the same Sail writeback state as `execute_DIVW ... true`.

DIVUW does not require raw 64-bit advice uniqueness: in the divisor-zero
case, multiple advice words can have low 32 bits `0xFFFFFFFF`. The
guards still force the post-`SignExtendWord` value written to `rd` to
be Sail's architectural DIVUW result. -/
theorem jolt_divuw_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_divuw rs2 rs1 rd q).run js = .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_divw_value dividend divisor true) := by
  rw [jolt_divuw_phased] at hok
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  -- PHASE 1 unpeel.
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run_sound rs1 rs2 q js js₁ _ dividend divisor
      hrs1 hrs2 hp1
  -- PHASE 2 unpeel.
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run_sound js₁ js₂ _ q zd zv
      h1_v0 h1_v1 h1_v2 hp2
  -- PHASE 3 unpeel.
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run_sound js₂ js₃ _ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hp3
  -- PHASE 4 unpeel.
  obtain ⟨_, js₄, hp4, hp5⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run_sound js₃ js₄ _ q zv
      h3_v1 h3_v2 hp4
  have h_sext :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value_of_guards_uw dividend divisor q
      hguard1 hguard2 hguard3 hguard4
  have h4_sail_orig : js₄.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hwrite :=
    Divuw.phase_writeback_run_sound rd js₄ js' js.sail RETIRE_SUCCESS
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig hp5
  rw [h_sext] at hwrite
  exact hwrite

end
