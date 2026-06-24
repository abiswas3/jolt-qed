import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.DivProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Program blocks for `remProgram`

REM shares DIV's advice, div0, overflow, and quotient-product checks.
The key difference is writeback: after the nested `MULH` block consumes
`v4`, `v5`, and `v6`, REM keeps the reconstructed signed remainder in `v8`
and writes `v8` to `rd`.
-/

namespace Rem

/-- Rust `a2`: quotient advice returned by the virtual-register allocator. -/
abbrev a2VReg : JoltISA.VReg := Div.a2VReg

/-- Rust `a3`: absolute-remainder advice returned by the allocator. -/
abbrev a3VReg : JoltISA.VReg := Div.a3VReg

/-- Rust `t0`: adjusted divisor used for the overflow edge case. -/
abbrev t0VReg : JoltISA.VReg := Div.t0VReg

/-- Rust `t1`: temporary register, also the nested `MULH` destination. -/
abbrev t1VReg : JoltISA.VReg := Div.t1VReg

/-- Rust `t2`: product register, later reused for `|adjusted_divisor|` in REM. -/
abbrev t2VReg : JoltISA.VReg := Div.t2VReg

/-- Rust `t3`: signed-remainder register that REM writes back. -/
abbrev t3VReg : JoltISA.VReg := Div.t3VReg

/-- Phase 1 — advice loads + div-by-zero assert. Same as DIV. -/
def phase_setup (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltISA.Program :=
  Div.phase_setup rs2 quotient rem_abs

/-- Phase 2 — adjusted divisor, MULH/MUL/SRAI, overflow-check assert. Same as DIV. -/
def phase_overflow_check (rs1 rs2 : regidx) : JoltISA.Program :=
  Div.phase_overflow_check rs1 rs2

/-- Phase 3 — reconstruct signed remainder in `v8`, sum, assert equals dividend. -/
def phase_quotient_product (rs1 : regidx) : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg t1VReg) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg t3VReg) (.vreg a3VReg) (.vreg t1VReg)) <|
  .instr (.SUB (.vreg t3VReg) (.vreg t3VReg) (.vreg t1VReg)) <|
  .instr (.ADD (.vreg t2VReg) (.vreg t2VReg) (.vreg t3VReg)) <|
  .instr (.VirtualAssertEQ (.vreg t2VReg) (.xreg rs1) (0 : BitVec 13)) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — compute `|adj_div|` into Rust `t2`, preserving signed remainder in `t3`. -/
def phase_remainder_bound : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg t1VReg) (.vreg t0VReg) (63 : BitVec 6) <|
  .instr (.XOR (.vreg t2VReg) (.vreg t0VReg) (.vreg t1VReg)) <|
  .instr (.SUB (.vreg t2VReg) (.vreg t2VReg) (.vreg t1VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg a3VReg) (.vreg t2VReg)) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — move Rust `t3`, the reconstructed signed remainder, into real register `rd`. -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg t3VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Phase 1 — advice loads + div-by-zero assert. -/
theorem phase_setup_run
    (rs2 : regidx) (q rem : BitVec 64) (js : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs2 q rem)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.sail = js.sail := by
  exact Div.phase_setup_run rs2 q rem js divisor hrs2 hguard_div0

/-- Phase 2 — adjusted divisor + MUL/MULH + overflow-check assert. -/
theorem phase_overflow_check_run
    (rs1 rs2 : regidx)
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63) :
    ∃ js',
      (JoltISA.execProgram (phase_overflow_check rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t2VReg = q * adj ∧
      js'.sail = js.sail := by
  exact Div.phase_overflow_check_run rs1 rs2 js q rem adj dividend divisor
    hrs1 hrs2 h_v0 h_v1 hadj hguard_overflow

/-- Phase 3 — signed-remainder reconstruction + `assert_eq_real v7 rs1`.

The returned `v8` value is the signed remainder that REM will write back. -/
theorem phase_quotient_product_run
    (rs1 : regidx)
    (js : SailJoltState)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v7 : js.vregs t2VReg = q * adj)
    (hguard_quotient_product :
        q * adj +
          ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
        = dividend) :
    ∃ js',
      (JoltISA.execProgram (phase_quotient_product rs1)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t3VReg =
        ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ :=
    JoltISA.srai_block_run_vreg_xreg_ex t1VReg rs1 63 js dividend hrs1 (by unfold WritableVReg; decide)
  obtain ⟨s2, h2, h2_v8, h2_pres, h2_sail⟩ := JoltISA.xor_run_vreg_vreg_vreg_ex t3VReg a3VReg t1VReg s1 (by unfold WritableVReg; decide)
  obtain ⟨s3, h3, h3_v8, h3_pres, h3_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex t3VReg t3VReg t1VReg s2 (by unfold WritableVReg; decide)
  obtain ⟨s4, h4, h4_v7, h4_pres, h4_sail⟩ := JoltISA.add_run_vreg_vreg_vreg_ex t2VReg t2VReg t3VReg s3 (by unfold WritableVReg; decide)
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hs1_v1 : s1.vregs a3VReg = rem := (h1_pres a3VReg (by decide)).trans h_v1
  have hs1_v3 : s1.vregs t1VReg = dividend.sshiftRight 63 := by rw [h1_v3]; rfl
  have hs1_v7 : s1.vregs t2VReg = q * adj := (h1_pres t2VReg (by decide)).trans h_v7
  have hs2_v3 : s2.vregs t1VReg = dividend.sshiftRight 63 :=
    (h2_pres t1VReg (by decide)).trans hs1_v3
  have hs2_v7 : s2.vregs t2VReg = q * adj := (h2_pres t2VReg (by decide)).trans hs1_v7
  have hs2_v8 : s2.vregs t3VReg = rem ^^^ dividend.sshiftRight 63 := by
    rw [h2_v8, hs1_v1, hs1_v3]
  have hs3_v7 : s3.vregs t2VReg = q * adj := (h3_pres t2VReg (by decide)).trans hs2_v7
  have hs3_v8 :
      s3.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [h3_v8, hs2_v8, hs2_v3]
  have hs4_v7 : s4.vregs t2VReg = dividend := by
    rw [h4_v7, hs3_v7, hs3_v8]
    exact hguard_quotient_product
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail := hs4_sail.symm ▸ hrs1
  have h5 : (JoltISA.execInstr (.VirtualAssertEQ (.vreg t2VReg) (.xreg rs1) (0 : BitVec 13))).run s4 =
      .ok RETIRE_SUCCESS s4 :=
    JoltISA.virtual_assert_eq_real_run_ok t2VReg rs1 s4 dividend hrs1_s4 hs4_v7
  have hs4_v0 : s4.vregs a2VReg = q :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres a2VReg (by decide)).trans h_v0
  have hs4_v1 : s4.vregs a3VReg = rem :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres a3VReg (by decide)).trans h_v1
  have hs4_v2 : s4.vregs t0VReg = adj :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres t0VReg (by decide)).trans h_v2
  have hs4_v8 :
      s4.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 :=
    (h4_pres t3VReg (by decide)).trans hs3_v8
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_v8, hs4_sail⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s4 h5]
  rfl

/-- Phase 4 — compute `|adj|` into `v7` and check `|rem| < |adj|`,
preserving signed remainder in `v8`. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v8 : js.vregs t3VReg = signedRem)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs t3VReg = signedRem ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ := JoltISA.srai_block_run_vreg_vreg_ex t1VReg t0VReg 63 js (by unfold WritableVReg; decide)
  obtain ⟨s2, h2, h2_v7, h2_pres, h2_sail⟩ := JoltISA.xor_run_vreg_vreg_vreg_ex t2VReg t0VReg t1VReg s1 (by unfold WritableVReg; decide)
  obtain ⟨s3, h3, h3_v7, h3_pres, h3_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex t2VReg t2VReg t1VReg s2 (by unfold WritableVReg; decide)
  have hs3_sail : s3.sail = js.sail := h3_sail.trans (h2_sail.trans h1_sail)
  have hs1_v2 : s1.vregs t0VReg = adj := (h1_pres t0VReg (by decide)).trans h_v2
  have hs1_v3 : s1.vregs t1VReg = adj.sshiftRight 63 := by rw [h1_v3, h_v2]; rfl
  have hs2_v3 : s2.vregs t1VReg = adj.sshiftRight 63 :=
    (h2_pres t1VReg (by decide)).trans hs1_v3
  have hs2_v7 : s2.vregs t2VReg = adj ^^^ adj.sshiftRight 63 := by
    rw [h2_v7, hs1_v2, hs1_v3]
  have hs3_v7 : s3.vregs t2VReg = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [h3_v7, hs2_v7, hs2_v3]
  have hs3_v1 : s3.vregs a3VReg = rem :=
    (chain_pres_3 h1_pres h2_pres h3_pres a3VReg (by decide)).trans h_v1
  have hguard_lt : s3.vregs t2VReg = 0#64 ∨ (s3.vregs a3VReg).toNat < (s3.vregs t2VReg).toNat := by
    rw [hs3_v1, hs3_v7]
    exact hguard_rem_bound
  have h4 : (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder (.vreg a3VReg) (.vreg t2VReg))).run s3
              = .ok RETIRE_SUCCESS s3 :=
    JoltISA.virtual_assert_valid_unsigned_remainder_run_ok a3VReg t2VReg s3 hguard_lt
  have hs3_v8 : s3.vregs t3VReg = signedRem :=
    (chain_pres_3 h1_pres h2_pres h3_pres t3VReg (by decide)).trans h_v8
  refine ⟨s3, ?_, hs3_v8, hs3_sail⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

/-- Phase 5 — writeback `rd := v8`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v8 : js.vregs t3VReg = signedRem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd signedRem := by
  unfold phase_writeback
  have hrem :
      js.vregs t3VReg + sign_extend (m := 64) (0 : BitVec 12) = signedRem := by
    rw [h_v8]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd signedRem js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := JoltISA.addi_run_xreg_vreg rd t3VReg 0 js s' (by rw [hrem]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd signedRem
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd signedRem js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas
-- ----------------------------------------------------------------------------

/-- Phase 1 soundness. -/
theorem phase_setup_run_sound
    (rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (JoltISA.execProgram (phase_setup rs2 q rem)).run js =
      .ok RETIRE_SUCCESS js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.sail = js.sail := by
  exact Div.phase_setup_run_sound rs2 q rem js js₁ divisor hrs2 hp

/-- Phase 2 soundness. -/
theorem phase_overflow_check_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hp : (JoltISA.execProgram (phase_overflow_check rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    mulhs q adj = (q * adj).sshiftRight 63 ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t0VReg = adj ∧
    js₁.vregs t2VReg = q * adj ∧
    js₁.sail = js.sail := by
  exact Div.phase_overflow_check_run_sound rs1 rs2 js js₁ q rem adj
    dividend divisor hrs1 hrs2 h_v0 h_v1 hadj hp

/-- Phase 3 soundness, including the reconstructed signed remainder in `v8`. -/
theorem phase_quotient_product_run_sound
    (rs1 : regidx)
    (js js₁ : SailJoltState)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v7 : js.vregs t2VReg = q * adj)
    (hp : (JoltISA.execProgram (phase_quotient_product rs1)).run js =
      .ok RETIRE_SUCCESS js₁) :
    q * adj +
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
      = dividend ∧
    js₁.vregs a2VReg = q ∧
    js₁.vregs a3VReg = rem ∧
    js₁.vregs t0VReg = adj ∧
    js₁.vregs t3VReg =
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) ∧
  js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.srai_block_run_vreg_xreg_ex t1VReg rs1 63 js dividend hrs1 (by unfold WritableVReg; decide)
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v8, hs2_pres, hs2_sail⟩ := JoltISA.xor_run_vreg_vreg_vreg_ex t3VReg a3VReg t1VReg s1 (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v8, hs3_pres, hs3_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex t3VReg t3VReg t1VReg s2 (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨s4, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s4, hrun4_ex, hs4_v7, hs4_pres, hs4_sail⟩ := JoltISA.add_run_vreg_vreg_vreg_ex t2VReg t2VReg t3VReg s3 (by unfold WritableVReg; decide)
  rw [hrun4_ex] at hrun4
  cases hrun4
  obtain ⟨js_afterAssert, hrun5, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v1 : s1.vregs a3VReg = rem := (hs1_pres a3VReg (by decide)).trans h_v1
  have hs1_v3' : s1.vregs t1VReg = dividend.sshiftRight 63 := by rw [hs1_v3]; rfl
  have hs1_v7 : s1.vregs t2VReg = q * adj := (hs1_pres t2VReg (by decide)).trans h_v7
  have hs2_v3 : s2.vregs t1VReg = dividend.sshiftRight 63 :=
    (hs2_pres t1VReg (by decide)).trans hs1_v3'
  have hs2_v7 : s2.vregs t2VReg = q * adj := (hs2_pres t2VReg (by decide)).trans hs1_v7
  have hs2_v8' : s2.vregs t3VReg = rem ^^^ dividend.sshiftRight 63 := by
    rw [hs2_v8, hs1_v1, hs1_v3']
  have hs3_v7 : s3.vregs t2VReg = q * adj := (hs3_pres t2VReg (by decide)).trans hs2_v7
  have hs3_v8' :
      s3.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [hs3_v8, hs2_v8', hs2_v3]
  have hs4_v7' :
      s4.vregs t2VReg =
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) := by
    rw [hs4_v7, hs3_v7, hs3_v8']
  have hs4_sail_orig : s4.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail :=
    hs4_sail_orig.symm ▸ hrs1
  by_cases hguard : s4.vregs t2VReg = dividend
  · have hguard_eq :
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
          = dividend := by
      rw [← hs4_v7']
      exact hguard
    have hs4_v0 : s4.vregs a2VReg = q :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres a2VReg (by decide)).trans h_v0
    have hs4_v1 : s4.vregs a3VReg = rem :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres a3VReg (by decide)).trans h_v1
    have hs4_v2 : s4.vregs t0VReg = adj :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres t0VReg (by decide)).trans h_v2
    have hs4_v8 :
        s4.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 :=
      (hs4_pres t3VReg (by decide)).trans hs3_v8'
    have hok := JoltISA.virtual_assert_eq_real_run_ok t2VReg rs1 s4 dividend hrs1_s4 hguard
    rw [hok] at hrun5
    cases hrun5
    exact ⟨hguard_eq, hs4_v0, hs4_v1, hs4_v2, hs4_v8, hs4_sail_orig⟩
  · exfalso
    have herr := JoltISA.virtual_assert_eq_real_run_err t2VReg rs1 s4 dividend hrs1_s4 hguard
    rw [herr] at hrun5
    cases hrun5

/-- Phase 4 soundness. -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (rem adj signedRem : BitVec 64)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (h_v8 : js.vregs t3VReg = signedRem)
    (hp : (JoltISA.execProgram phase_remainder_bound).run js =
      .ok RETIRE_SUCCESS js₁) :
    (((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) ∧
    js₁.vregs t3VReg = signedRem ∧
  js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := JoltISA.srai_block_run_vreg_vreg_ex t1VReg t0VReg 63 js (by unfold WritableVReg; decide)
  rw [hrun1_ex _] at hp
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s2, hrun2_ex, hs2_v7, hs2_pres, hs2_sail⟩ := JoltISA.xor_run_vreg_vreg_vreg_ex t2VReg t0VReg t1VReg s1 (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s3, hrun3_ex, hs3_v7, hs3_pres, hs3_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex t2VReg t2VReg t1VReg s2 (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨js_afterAssert, hrun4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v2 : s1.vregs t0VReg = adj := (hs1_pres t0VReg (by decide)).trans h_v2
  have hs1_v3' : s1.vregs t1VReg = adj.sshiftRight 63 := by rw [hs1_v3, h_v2]; rfl
  have hs2_v3 : s2.vregs t1VReg = adj.sshiftRight 63 :=
    (hs2_pres t1VReg (by decide)).trans hs1_v3'
  have hs2_v7' : s2.vregs t2VReg = adj ^^^ adj.sshiftRight 63 := by
    rw [hs2_v7, hs1_v2, hs1_v3']
  have hs3_v7' :
      s3.vregs t2VReg = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [hs3_v7, hs2_v7', hs2_v3]
  have hs3_v1 : s3.vregs a3VReg = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)).trans h_v1
  have hs3_v8 : s3.vregs t3VReg = signedRem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres t3VReg (by decide)).trans h_v8
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  by_cases hguard : s3.vregs t2VReg = 0#64 ∨ (s3.vregs a3VReg).toNat < (s3.vregs t2VReg).toNat
  · have hok := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok a3VReg t2VReg s3 hguard
    rw [hok] at hrun4
    cases hrun4
    refine ⟨?_, hs3_v8, hs3_sail_orig⟩
    rcases hguard with h0 | hlt
    · left; rw [← hs3_v7']; exact h0
    · right; rw [← hs3_v1, ← hs3_v7']; exact hlt
  · exfalso
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err a3VReg t2VReg s3 hguard
    rw [herr] at hrun4
    cases hrun4

/-- Phase 5 soundness. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (signedRem : BitVec 64)
    (h_v8 : js.vregs t3VReg = signedRem)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd signedRem := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hrem :
      js.vregs t3VReg + sign_extend (m := 64) (0 : BitVec 12) = signedRem := by
    rw [h_v8]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd signedRem js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg t3VReg) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    JoltISA.addi_run_xreg_vreg rd t3VReg 0 js s' (by rw [hrem]; exact hw)
  rw [hp_concrete] at hrun
  cases hrun
  show s' = stateAfterWrite js_ref rd signedRem
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd signedRem js.sail s' hw

end Rem

end
