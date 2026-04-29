import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divu_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_remu`

REMU uses one virtual register.  `v0` starts as quotient advice, then is
overwritten by `q * divisor`, then by the computed remainder.
-/

namespace Remu

def phase_setup (quotient : BitVec 64) : JoltMonad ExecutionResult :=
  vreg_advice 0 quotient

def phase_overflow_check (rs2 : regidx) : JoltMonad ExecutionResult :=
  vreg_assert_mulu_no_overflow 0 rs2

def phase_quotient_product (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_MUL_from_real_vs2 0 0 rs2
  vreg_assert_lte_real 0 rs1

def phase_remainder_bound (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_SUB_from_real_vs1 0 rs1 0
  vreg_assert_valid_unsigned_remainder_real 0 rs2

def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_ADDI_to_real rd 0 0

theorem phase_setup_run
    (q : BitVec 64) (js : SailJoltState) :
    ∃ js',
      (phase_setup q).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨js', hrun, h_v0, _, h_sail⟩ := vreg_advice_run_ex 0 q js
  exact ⟨js', hrun, h_v0, h_sail⟩

theorem phase_overflow_check_run
    (rs2 : regidx) (js : SailJoltState) (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_no_overflow : q.toNat * divisor.toNat < 2^64) :
    ∃ js',
      (phase_overflow_check rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  have hguard : (js.vregs 0).toNat * divisor.toNat < 2^64 := h_v0 ▸ hguard_no_overflow
  have hrun : vreg_assert_mulu_no_overflow 0 rs2 js = .ok RETIRE_SUCCESS js :=
    vreg_assert_mulu_no_overflow_run_ok 0 rs2 js divisor hrs2 hguard
  exact ⟨js, hrun, h_v0, rfl⟩

theorem phase_quotient_product_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hguard_lte : (q * divisor).toNat ≤ dividend.toNat) :
    ∃ js',
      (phase_quotient_product rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q * divisor ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v0, _, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex 0 0 rs2 js divisor hrs2
  have hs1_v0_eq : s1.vregs 0 = q * divisor := by rw [hs1_v0, h_v0]
  have hrs1_s1 : rX_bits rs1 s1.sail = .ok dividend s1.sail := hs1_sail.symm ▸ hrs1
  have hguard : (s1.vregs 0).toNat ≤ dividend.toNat := by
    rw [hs1_v0_eq]
    exact hguard_lte
  have h2 : vreg_assert_lte_real 0 rs1 s1 = .ok RETIRE_SUCCESS s1 :=
    vreg_assert_lte_real_run_ok 0 rs1 s1 dividend hrs1_s1 hguard
  refine ⟨s1, ?_, hs1_v0_eq, hs1_sail⟩
  rw [bind_run_of_ok h1]
  exact h2

theorem phase_remainder_bound_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q * divisor)
    (hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    ∃ js',
      (phase_remainder_bound rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = dividend - q * divisor ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v0, _, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex 0 rs1 0 js dividend hrs1
  have hs1_v0_eq : s1.vregs 0 = dividend - q * divisor := by rw [hs1_v0, h_v0]
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail := hs1_sail.symm ▸ hrs2
  have hguard : divisor = 0#64 ∨ (s1.vregs 0).toNat < divisor.toNat := by
    rw [hs1_v0_eq]
    exact hguard_rem_bound
  have h2 : vreg_assert_valid_unsigned_remainder_real 0 rs2 s1
      = .ok RETIRE_SUCCESS s1 :=
    vreg_assert_valid_unsigned_remainder_real_run_ok 0 rs2 s1 divisor hrs2_s1 hguard
  refine ⟨s1, ?_, hs1_v0_eq, hs1_sail⟩
  rw [bind_run_of_ok h1]
  exact h2

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v0 : js.vregs 0 = rem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd rem := by
  unfold phase_writeback
  have hrem : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = rem := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd rem js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · show vreg_ADDI_to_real rd 0 0 js = _
    exact vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hrem]; exact hw)
  · show s' = stateAfterWrite js_ref rd rem
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd rem js.sail s' hw

theorem phase_setup_run_sound
    (q : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (hp : (phase_setup q).run js = .ok r js₁) :
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_setup at hp
  obtain ⟨s₁, hrun, hs1_v0, _, hs1_sail⟩ := vreg_advice_run_ex 0 q js
  rw [hrun] at hp
  cases hp
  exact ⟨hs1_v0, hs1_sail⟩

theorem phase_overflow_check_run_sound
    (rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (phase_overflow_check rs2).run js = .ok r js₁) :
    q.toNat * divisor.toNat < 2^64 ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_overflow_check at hp
  by_cases hguard : (js.vregs 0).toNat * divisor.toNat < 2^64
  · have hok := vreg_assert_mulu_no_overflow_run_ok 0 rs2 js divisor hrs2 hguard
    change vreg_assert_mulu_no_overflow 0 rs2 js = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    exact ⟨h_v0 ▸ hguard, h_v0, rfl⟩
  · exfalso
    have herr := vreg_assert_mulu_no_overflow_run_err 0 rs2 js divisor hrs2 hguard
    change vreg_assert_mulu_no_overflow 0 rs2 js = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

theorem phase_quotient_product_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (hp : (phase_quotient_product rs1 rs2).run js = .ok r js₁) :
    (q * divisor).toNat ≤ dividend.toNat ∧
    js₁.vregs 0 = q * divisor ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, _, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex 0 0 rs2 js divisor hrs2
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v0_eq : s₁.vregs 0 = q * divisor := by rw [hs1_v0, h_v0]
  have hrs1_s1 : rX_bits rs1 s₁.sail = .ok dividend s₁.sail := hs1_sail.symm ▸ hrs1
  by_cases hguard : (s₁.vregs 0).toNat ≤ dividend.toNat
  · have hok := vreg_assert_lte_real_run_ok 0 rs1 s₁ dividend hrs1_s1 hguard
    change vreg_assert_lte_real 0 rs1 s₁ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    exact ⟨hs1_v0_eq ▸ hguard, hs1_v0_eq, hs1_sail⟩
  · exfalso
    have herr := vreg_assert_lte_real_run_err 0 rs1 s₁ dividend hrs1_s1 hguard
    change vreg_assert_lte_real 0 rs1 s₁ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

theorem phase_remainder_bound_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q * divisor)
    (hp : (phase_remainder_bound rs1 rs2).run js = .ok r js₁) :
    (divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) ∧
    js₁.vregs 0 = dividend - q * divisor ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, _, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex 0 rs1 0 js dividend hrs1
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v0_eq : s₁.vregs 0 = dividend - q * divisor := by rw [hs1_v0, h_v0]
  have hrs2_s1 : rX_bits rs2 s₁.sail = .ok divisor s₁.sail := hs1_sail.symm ▸ hrs2
  by_cases hguard : divisor = 0#64 ∨ (s₁.vregs 0).toNat < divisor.toNat
  · have hok :=
      vreg_assert_valid_unsigned_remainder_real_run_ok 0 rs2 s₁ divisor hrs2_s1 hguard
    change vreg_assert_valid_unsigned_remainder_real 0 rs2 s₁ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    refine ⟨?_, hs1_v0_eq, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left
      exact h0
    · right
      rw [← hs1_v0_eq]
      exact hlt
  · exfalso
    have herr :=
      vreg_assert_valid_unsigned_remainder_real_run_err 0 rs2 s₁ divisor hrs2_s1 hguard
    change vreg_assert_valid_unsigned_remainder_real 0 rs2 s₁ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (rem : BitVec 64)
    (h_v0 : js.vregs 0 = rem)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd rem := by
  unfold phase_writeback at hp
  change vreg_ADDI_to_real rd 0 0 js = .ok r js₁ at hp
  have hrem : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = rem := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd rem js.sail
  have hp_concrete : vreg_ADDI_to_real rd 0 0 js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hrem]; exact hw)
  rw [hp_concrete] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd rem
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd rem js.sail s' hw

end Remu

end
