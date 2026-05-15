import JoltBytecode.JoltISA.Environment
import JoltBytecode.JoltISA.Semantics.RegisterOps
import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw_math
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw_phase_helpers

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMUW: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/remuw.rs::inline_sequence`.
REMUW computes an unsigned 32-bit remainder and sign-extends that
32-bit result to 64 bits.
-/

def jolt_remuw (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_zero_extend_word_from_real 0 rs1            -- VirtualZeroExtendWord v0, rs1, 0
  let _ ← vreg_zero_extend_word_from_real 1 rs2            -- VirtualZeroExtendWord v1, rs2, 0
  let _ ← vreg_advice 2 quotient                           -- VirtualAdvice v2, 0
  let _ ← vreg_assert_mulu_no_overflow_v 2 1               -- VirtualAssertMulUNoOverflow v2, v1, 0
  let _ ← vreg_MUL 3 2 1                                   -- MUL v3, v2, v1
  let _ ← vreg_assert_lte 3 0                              -- VirtualAssertLTE v3, v0, 0
  let _ ← vreg_SUB 3 0 3                                   -- SUB v3, v0, v3
  let _ ← vreg_assert_valid_unsigned_remainder 3 1         -- VirtualAssertValidUnsignedRemainder v3, v1, 0
  vreg_sign_extend_word_to_real rd 3                       -- VirtualSignExtendWord rd, v3, 0

theorem jolt_remuw_phased (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) :
    jolt_remuw rs2 rs1 rd quotient = (do
      let _ ← Remuw.phase_setup rs1 rs2 quotient
      let _ ← Remuw.phase_quotient_product
      let _ ← Remuw.phase_remainder_bound
      Remuw.phase_writeback rd) := by
  simp [jolt_remuw, Remuw.phase_setup, Remuw.phase_quotient_product,
        Remuw.phase_remainder_bound, Remuw.phase_writeback,
        Divuw.phase_setup, Divuw.phase_quotient_product,
        Divuw.phase_remainder_bound, bind_assoc]

theorem jolt_remuw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_remuw rs2 rs1 rd
          (sail_divuw_advice dividend divisor)).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_remw_value dividend divisor true) := by
  let q  := sail_divuw_advice dividend divisor
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let rem := zd - q * zv
  have hguard_no_overflow : q.toNat * zv.toNat < 2^64 :=
    hguard_no_overflow_of_honest_uw dividend divisor
  have hguard_lte : (q * zv).toNat ≤ zd.toNat :=
    hguard_q_times_d_le_dividend_of_honest_uw dividend divisor
  have hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat :=
    hguard_rem_bound_of_honest_uw dividend divisor
  have hrem :
      sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0) =
        sail_remw_value dividend divisor true := by
    unfold rem
    exact signExtend_remainder_eq_sail_remw_of_guards_uw dividend divisor q
      hguard_no_overflow hguard_lte hguard_rem_bound
  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remuw.phase_setup_run rs1 rs2 q js dividend divisor hrs1 hrs2 hguard_no_overflow
  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Remuw.phase_quotient_product_run js₁ q zd zv
      h1_v0 h1_v1 h1_v2 hguard_lte
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨js₃, hrun3, h3_v3, h3_sail⟩ :=
    Remuw.phase_remainder_bound_run js₂ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hguard_rem_bound
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have h3_v3_rem : js₃.vregs 3 = rem := by
    unfold rem
    exact h3_v3
  obtain ⟨js₄, hrun4, h4_sail⟩ :=
    Remuw.phase_writeback_run rd js₃ js.sail rem h3_v3_rem h3_sail_orig
  refine ⟨js₄, ?_, ?_⟩
  · rw [jolt_remuw_phased]
    rw [bind_run_of_ok hrun1]
    rw [bind_run_of_ok hrun2]
    rw [bind_run_of_ok hrun3]
    exact hrun4
  · rw [hrem] at h4_sail
    exact h4_sail

theorem execute_REMUW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_remw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REMW, sail_remw_value, bind_pure_comp]

theorem execute_REMUW_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REMW rs2 rs1 rd true).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_remw_value dividend divisor true)) := by
  rw [execute_REMUW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_remw_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_remuw_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_remuw rs2 rs1 rd
                      (sail_divuw_advice dividend divisor)).run js) =
    (execute_REMW rs2 rs1 rd true).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_remuw_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_REMUW_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

theorem jolt_remuw_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_remuw rs2 rs1 rd q).run js = .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_remw_value dividend divisor true) := by
  rw [jolt_remuw_phased] at hok
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  let rem := zd - q * zv
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remuw.phase_setup_run_sound rs1 rs2 q js js₁ _ dividend divisor
      hrs1 hrs2 hp1
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Remuw.phase_quotient_product_run_sound js₁ js₂ _ q zd zv
      h1_v0 h1_v1 h1_v2 hp2
  obtain ⟨_, js₃, hp3, hp4⟩ := bind_unpeel_of_ok hok
  obtain ⟨hguard3, h3_v3, h3_sail⟩ :=
    Remuw.phase_remainder_bound_run_sound js₂ js₃ _ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hp3
  have h3_sail_orig : js₃.sail = js.sail :=
    h3_sail.trans (h2_sail.trans h1_sail)
  have hrem :
      sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0) =
        sail_remw_value dividend divisor true := by
    unfold rem
    exact signExtend_remainder_eq_sail_remw_of_guards_uw dividend divisor q
      hguard1 hguard2 hguard3
  have h3_v3_rem : js₃.vregs 3 = rem := by
    unfold rem
    exact h3_v3
  have hwrite :=
    Remuw.phase_writeback_run_sound rd js₃ js' js.sail RETIRE_SUCCESS
      rem h3_v3_rem h3_sail_orig hp4
  rw [hrem] at hwrite
  exact hwrite

end
