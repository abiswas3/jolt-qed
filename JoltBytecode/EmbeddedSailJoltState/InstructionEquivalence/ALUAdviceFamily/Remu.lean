import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.RegisterOps
import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Divu_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Remu_math
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Remu_phase_helpers

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# REMU: Jolt inline sequence with oracle advice

Transcribed from `tracer/src/instruction/remu.rs::inline_sequence` at
`XLEN = 64`.  The quotient advice is used only to compute and validate
the remainder; the final writeback is the inline-computed remainder.
-/

def jolt_remu (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) : JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                              -- VirtualAdvice v0, 0
  let _ ← vreg_assert_mulu_no_overflow 0 rs2                  -- VirtualAssertMulUNoOverflow v0, rs2, 0
  let _ ← vreg_MUL_from_real_vs2 0 0 rs2                      -- MUL v0, v0, rs2
  let _ ← vreg_assert_lte_real 0 rs1                          -- VirtualAssertLTE v0, rs1, 0
  let _ ← vreg_SUB_from_real_vs1 0 rs1 0                      -- SUB v0, rs1, v0
  let _ ← vreg_assert_valid_unsigned_remainder_real 0 rs2     -- VirtualAssertValidUnsignedRemainder v0, rs2, 0
  vreg_ADDI_to_real rd 0 0                                    -- ADDI rd, v0, 0

theorem jolt_remu_phased (rs2 rs1 rd : regidx)
    (quotient : BitVec 64) :
    jolt_remu rs2 rs1 rd quotient = (do
      let _ ← Remu.phase_setup quotient
      let _ ← Remu.phase_overflow_check rs2
      let _ ← Remu.phase_quotient_product rs1 rs2
      let _ ← Remu.phase_remainder_bound rs1 rs2
      Remu.phase_writeback rd) := by
  simp [jolt_remu, Remu.phase_setup, Remu.phase_overflow_check,
        Remu.phase_quotient_product, Remu.phase_remainder_bound,
        Remu.phase_writeback, bind_assoc]

theorem jolt_remu_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (jolt_remu rs2 rs1 rd
          (sail_div_value dividend divisor true)).run js
        = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
                   (sail_rem_value dividend divisor true) := by
  let q := sail_div_value dividend divisor true
  let rem := dividend - q * divisor
  have hguard_no_overflow : q.toNat * divisor.toNat < 2^64 :=
    hguard_no_overflow_of_honest_u dividend divisor
  have hguard_lte : (q * divisor).toNat ≤ dividend.toNat :=
    hguard_q_times_d_le_dividend_of_honest_u dividend divisor
  have hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat :=
    hguard_rem_bound_of_honest_u dividend divisor
  have hrem : rem = sail_rem_value dividend divisor true := by
    unfold rem
    exact remainder_eq_sail_rem_of_guards_u dividend divisor q
      hguard_no_overflow hguard_lte hguard_rem_bound
  obtain ⟨js₁, hrun1, h1_v0, h1_sail⟩ :=
    Remu.phase_setup_run q js
  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_sail⟩ :=
    Remu.phase_overflow_check_run rs2 js₁ q divisor
      hrs2_js1 h1_v0 hguard_no_overflow
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_js2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨js₃, hrun3, h3_v0, h3_sail⟩ :=
    Remu.phase_quotient_product_run rs1 rs2 js₂ q dividend divisor
      hrs1_js2 hrs2_js2 h2_v0 hguard_lte
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have hrs1_js3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_js3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    Remu.phase_remainder_bound_run rs1 rs2 js₃ q dividend divisor
      hrs1_js3 hrs2_js3 h3_v0 hguard_rem_bound
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have h4_v0_rem : js₄.vregs 0 = rem := by
    unfold rem
    exact h4_v0
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Remu.phase_writeback_run rd js₄ js.sail rem h4_v0_rem h4_sail_orig
  refine ⟨js₅, ?_, ?_⟩
  · rw [jolt_remu_phased]
    rw [bind_run_of_ok hrun1]
    rw [bind_run_of_ok hrun2]
    rw [bind_run_of_ok hrun3]
    rw [bind_run_of_ok hrun4]
    exact hrun5
  · rw [hrem] at h5_sail
    exact h5_sail

theorem execute_REMU_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REM, sail_rem_value, bind_pure_comp]

theorem execute_REMU_reduces (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REM rs2 rs1 rd true).run js.sail
      = .ok RETIRE_SUCCESS
          (stateAfterWrite js.sail rd
             (sail_rem_value dividend divisor true)) := by
  rw [execute_REMU_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_rem_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem jolt_remu_complete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    projectResult ((jolt_remu rs2 rs1 rd
                      (sail_div_value dividend divisor true)).run js) =
    (execute_REM rs2 rs1 rd true).run js.sail := by
  obtain ⟨js', hjolt, hjolt_sail⟩ :=
    jolt_remu_concrete rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2
  rw [hjolt]
  simp only [projectResult, project]
  rw [hjolt_sail]
  rw [execute_REMU_reduces rs2 rs1 rd hrd js hwf dividend divisor hrs1 hrs2]

theorem jolt_remu_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (js' : SailJoltState)
    (hok : (jolt_remu rs2 rs1 rd q).run js = .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_rem_value dividend divisor true) := by
  rw [jolt_remu_phased] at hok
  let rem := dividend - q * divisor
  obtain ⟨_, js₁, hp1, hok⟩ := bind_unpeel_of_ok hok
  obtain ⟨h1_v0, h1_sail⟩ :=
    Remu.phase_setup_run_sound q js js₁ _ hp1
  obtain ⟨_, js₂, hp2, hok⟩ := bind_unpeel_of_ok hok
  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard1, h2_v0, h2_sail⟩ :=
    Remu.phase_overflow_check_run_sound rs2 js₁ js₂ _ q divisor
      hrs2_1 h1_v0 hp2
  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨_, js₃, hp3, hok⟩ := bind_unpeel_of_ok hok
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨hguard2, h3_v0, h3_sail⟩ :=
    Remu.phase_quotient_product_run_sound rs1 rs2 js₂ js₃ _ q dividend divisor
      hrs1_2 hrs2_2 h2_v0 hp3
  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨_, js₄, hp4, hp5⟩ := bind_unpeel_of_ok hok
  have hrs1_3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨hguard3, h4_v0, h4_sail⟩ :=
    Remu.phase_remainder_bound_run_sound rs1 rs2 js₃ js₄ _ q dividend divisor
      hrs1_3 hrs2_3 h3_v0 hp4
  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  have hrem : rem = sail_rem_value dividend divisor true := by
    unfold rem
    exact remainder_eq_sail_rem_of_guards_u dividend divisor q
      hguard1 hguard2 hguard3
  have h4_v0_rem : js₄.vregs 0 = rem := by
    unfold rem
    exact h4_v0
  have hwrite :=
    Remu.phase_writeback_run_sound rd js₄ js' js.sail RETIRE_SUCCESS
      rem h4_v0_rem h4_sail_orig hp5
  rw [hrem] at hwrite
  exact hwrite

end
