import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_phase_helpers
import JoltBytecode.JoltISA.Semantics.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `remuwProgram`

REMUW shares DIVUW's zero-extension prologue and quotient-product
checks, but keeps the computed remainder in `v3` and sign-extends that
value to the real destination register.
-/

namespace Remuw

def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) :
    JoltISA.Program :=
  Divuw.phase_setup rs1 rs2 quotient

def phase_quotient_product : JoltISA.Program :=
  Divuw.phase_quotient_product

def phase_remainder_bound : JoltISA.Program :=
  Divuw.phase_remainder_bound

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg 3)) <|
  .done RETIRE_SUCCESS

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
      (JoltISA.execProgram (phase_setup rs1 rs2 q)).run js = .ok RETIRE_SUCCESS js' ∧
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
      (JoltISA.execProgram phase_quotient_product).run js = .ok RETIRE_SUCCESS js' ∧
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
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
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
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v3 : js.vregs 3 = rem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have h1 : (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg 3))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
      apply vreg_sign_extend_word_to_real_run rd 3 js s'
      rw [h_v3]
      exact hw
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } h1]
    rfl
  · show s' = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : JoltISA.Program.Run (phase_setup rs1 rs2 q) js js₁) :
    q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64 ∧
    js₁.vregs 0 = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.vregs 1 = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs 2 = q ∧
    js₁.sail = js.sail := by
  exact Divuw.phase_setup_run_sound rs1 rs2 q js js₁ dividend divisor hrs1 hrs2 hp

theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (hp : JoltISA.Program.Run phase_quotient_product js js₁) :
    (q * zv).toNat ≤ zd.toNat ∧
    js₁.vregs 0 = zd ∧
    js₁.vregs 1 = zv ∧
    js₁.vregs 2 = q ∧
    js₁.vregs 3 = q * zv ∧
    js₁.sail = js.sail := by
  exact Divuw.phase_quotient_product_run_sound js js₁ q zd zv h_v0 h_v1 h_v2 hp

theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs 0 = zd)
    (h_v1 : js.vregs 1 = zv)
    (h_v2 : js.vregs 2 = q)
    (h_v3 : js.vregs 3 = q * zv)
    (hp : JoltISA.Program.Run phase_remainder_bound js js₁) :
    (zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) ∧
    js₁.vregs 3 = zd - q * zv ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_remainder_bound Divuw.phase_remainder_bound at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SUB_run_ex 3 0 3 js
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v1 : s1.vregs 1 = zv := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs 3 = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertValidUnsignedRemainder 3 1) (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : s1.vregs 1 = 0#64 ∨ (s1.vregs 3).toNat < (s1.vregs 1).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 3 1 s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
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
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v3 : js.vregs 3 = rem)
    (h_sail : js.sail = js_ref)
    (hp : JoltISA.Program.Run (phase_writeback rd) js js₁) :
    js₁.sail = stateAfterWrite js_ref rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold JoltISA.Program.Run phase_writeback at hp
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  have hrun :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg 3))).run js =
        .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd 3 js s' (by rw [h_v3]; exact hw)
  rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Remuw

end
