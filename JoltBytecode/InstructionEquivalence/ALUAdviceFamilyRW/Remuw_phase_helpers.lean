import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_remuw`

REMUW shares DIVUW's zero-extension prologue and quotient-product
checks, but keeps the computed remainder in `v3` and sign-extends that
value to the real destination register.
-/

namespace Remuw

def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) :
    JoltMonad ExecutionResult :=
  Divuw.phase_setup rs1 rs2 quotient

def phase_quotient_product : JoltMonad ExecutionResult :=
  Divuw.phase_quotient_product

def phase_remainder_bound : JoltMonad ExecutionResult :=
  Divuw.phase_remainder_bound

def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_sign_extend_word_to_real rd 3

theorem phase_setup_run
    (rs1 rs2 : regidx) (q : BitVec 64) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_no_overflow :
      q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64) :
    ∃ js',
      (phase_setup rs1 rs2 q).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs 2 = q ∧
      js'.sail = js.sail := by
  exact Divuw.phase_setup_run rs1 rs2 q js dividend divisor hrs1 hrs2 hguard_no_overflow

theorem phase_quotient_product_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hguard_lte : (q * zv).toNat ≤ zd.toNat) :
    ∃ js',
      phase_quotient_product.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = zd ∧
      js'.vregs 1 = zv ∧
      js'.vregs 2 = q ∧
      js'.vregs 3 = q * zv ∧
      js'.sail = js.sail := by
  exact Divuw.phase_quotient_product_run js q zd zv h_v0 h_v1 h_v2 hguard_lte

theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) :
    ∃ js',
      phase_remainder_bound.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 3 = zd - q * zv ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound Divuw.phase_remainder_bound
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SUB_run_ex 3 0 3 js
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs 3 = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  have hguard : s1.vregs 1 = 0#64 ∨ (s1.vregs 3).toNat < (s1.vregs 1).toNat := by
    rw [hs1_v3_eq, hs1_v1]
    exact hguard_rem_bound
  have h2 := vreg_assert_valid_unsigned_remainder_run_ok 3 1 s1 hguard
  refine ⟨s1, ?_, hs1_v3_eq, hs1_sail⟩
  rw [bind_run_of_ok h1]
  exact h2

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v3 : js.vregs 3 = rem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · show vreg_sign_extend_word_to_real rd 3 js = _
    apply vreg_sign_extend_word_to_real_run rd 3 js s'
    rw [h_v3]
    exact hw
  · show s' = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs1 rs2 q).run js = .ok r js₁) :
    q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64 ∧
    js₁.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  exact Divuw.phase_setup_run_sound rs1 rs2 q js js₁ r dividend divisor hrs1 hrs2 hp

theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : phase_quotient_product.run js = .ok r js₁) :
    (q * zv).toNat ≤ zd.toNat ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.vregs 3 = q * zv ∧
    js₁.sail = js.sail := by
  exact Divuw.phase_quotient_product_run_sound js js₁ r q zd zv h_v0 h_v1 h_v2 hp

theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hp : phase_remainder_bound.run js = .ok r js₁) :
    (zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) ∧
    js₁.vregs 3 = zd - q * zv ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound Divuw.phase_remainder_bound at hp
  obtain ⟨_, s1, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SUB_run_ex 3 0 3 js
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs 3 = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  change vreg_assert_valid_unsigned_remainder 3 1 s1 = .ok r js₁ at hp
  by_cases hguard : s1.vregs 1 = 0#64 ∨ (s1.vregs 3).toNat < (s1.vregs 1).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 3 1 s1 hguard
    rw [hok] at hp
    cases hp
    refine ⟨?_, hs1_v3_eq, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left
      exact hs1_v1.symm.trans h0
    · right
      rw [hs1_v3_eq, hs1_v1] at hlt
      exact hlt
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err 3 1 s1 hguard
    rw [herr] at hp
    cases hp

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (rem : BitVec 64)
    (h_v3 : js.vregs 3 = rem)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold phase_writeback at hp
  change vreg_sign_extend_word_to_real rd 3 js = .ok r js₁ at hp
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  have hrun : vreg_sign_extend_word_to_real rd 3 js = .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd 3 js s' (by rw [h_v3]; exact hw)
  rw [hrun] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Remuw

end
