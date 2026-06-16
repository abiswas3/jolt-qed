import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives
import JoltBytecode.InstructionEquivalence.MonadReduction
import JoltBytecode.JoltISA.Semantics.ProgramComposition
import JoltBytecode.JoltISA.Semantics.InstructionRunHelpers
import JoltBytecode.JoltISA.Semantics.ExpansionBlocks.Mul

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `divProgram`

The 18 instructions of the `DIV` bytecode expansion split into five phases,
each one ending at (or dominated by) an assertion. This file holds:

* the **phase definitions** (`JoltISA.Program` fragments, each a 1–5 step
  sub-sequence of the bytecode expansion),
* the **phase-run lemmas** — one per phase — characterising what each
  phase produces given its preconditions and guards.
-/

-- ----------------------------------------------------------------------------
-- Phase definitions
-- ----------------------------------------------------------------------------

namespace Div

/-- Rust `a2`: quotient advice returned by the virtual-register allocator. -/
abbrev a2VReg : JoltISA.VReg := JoltISA.inlineTmp0

/-- Rust `a3`: absolute-remainder advice returned by the allocator. -/
abbrev a3VReg : JoltISA.VReg := JoltISA.inlineTmp1

/-- Rust `t0`: adjusted divisor used for the overflow edge case. -/
abbrev t0VReg : JoltISA.VReg := JoltISA.inlineTmp2

/-- Rust `t1`: temporary register, also the nested `MULH` destination. -/
abbrev t1VReg : JoltISA.VReg := JoltISA.inlineTmp3

/-- Rust `t2`: allocated after the nested `MULH` returns. -/
abbrev t2VReg : JoltISA.VReg := JoltISA.inlineTmp4

/-- Rust `t3`: allocated after the nested `MULH` returns. -/
abbrev t3VReg : JoltISA.VReg := JoltISA.inlineTmp5

/-- Nested `MULH` scratch after `a2/a3/t0/t1` are live; Rust has no outer name for it. -/
abbrev t4VReg : JoltISA.VReg := JoltISA.inlineTmp6

/-- Phase 1 — advice loads + div-by-zero assert. -/
def phase_setup (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltISA.Program :=
  .instr (.VirtualAdvice a2VReg quotient) <|
  .instr (.VirtualAdvice a3VReg rem_abs) <|
  .instr (.VirtualAssertValidDiv0 rs2 a2VReg) <|
  .done RETIRE_SUCCESS

/-- Phase 2 — adjusted divisor, MULH/MUL/SRAI, overflow-check assert. -/
def phase_overflow_check (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.VirtualChangeDivisor t0VReg rs1 rs2) <|
  JoltISA.mulhBlock t2VReg t3VReg t4VReg
    (.vreg t1VReg) (.vreg a2VReg) (.vreg t0VReg) <|
  .instr (.MUL (.vreg t2VReg) (.vreg a2VReg) (.vreg t0VReg)) <|
  JoltISA.sraiBlock (.vreg t3VReg) (.vreg t2VReg) (63 : BitVec 6) <|
  .instr (.VirtualAssertEQ t1VReg t3VReg) <|
  .done RETIRE_SUCCESS

/-- Phase 3 — reconstruct signed remainder, sum, assert equals dividend. -/
def phase_quotient_product (rs1 : regidx) : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg t1VReg) (.xreg rs1) (63 : BitVec 6) <|
  .instr (.XOR (.vreg t3VReg) (.vreg a3VReg) (.vreg t1VReg)) <|
  .instr (.SUB (.vreg t3VReg) (.vreg t3VReg) (.vreg t1VReg)) <|
  .instr (.ADD (.vreg t2VReg) (.vreg t2VReg) (.vreg t3VReg)) <|
  .instr (.VirtualAssertEQReal t2VReg rs1) <|
  .done RETIRE_SUCCESS

/-- Phase 4 — compute |adj_div|, assert |r| < |adj_div|. -/
def phase_remainder_bound : JoltISA.Program :=
  JoltISA.sraiBlock (.vreg t1VReg) (.vreg t0VReg) (63 : BitVec 6) <|
  .instr (.XOR (.vreg t3VReg) (.vreg t0VReg) (.vreg t1VReg)) <|
  .instr (.SUB (.vreg t3VReg) (.vreg t3VReg) (.vreg t1VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder a3VReg t3VReg) <|
  .done RETIRE_SUCCESS

/-- Phase 5 — move the quotient advice from v0 into real register rd. -/
def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg a2VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

-- ----------------------------------------------------------------------------
-- Phase-run lemmas
-- ----------------------------------------------------------------------------

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
  unfold phase_setup
  let s1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = a2VReg then q else js.vregs r }
  let s2 : SailJoltState :=
    { sail := s1.sail
      vregs := fun r => if r = a3VReg then rem else s1.vregs r }
  have h1 : (JoltISA.execInstr (.VirtualAdvice a2VReg q)).run js =
      .ok RETIRE_SUCCESS s1 := vreg_advice_run a2VReg q js (by unfold WritableVReg; decide)
  have h2 : (JoltISA.execInstr (.VirtualAdvice a3VReg rem)).run s1 =
      .ok RETIRE_SUCCESS s2 := vreg_advice_run a3VReg rem s1 (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs a2VReg = q := by
    show (if a2VReg = a3VReg then rem else s1.vregs a2VReg) = q
    rw [if_neg (by decide : a2VReg ≠ a3VReg)]
    show (if a2VReg = a2VReg then q else js.vregs a2VReg) = q
    rw [if_pos rfl]
  have hs2_v1 : s2.vregs a3VReg = rem := by
    show (if a3VReg = a3VReg then rem else s1.vregs a3VReg) = rem
    rw [if_pos rfl]
  have hs2_sail : s2.sail = js.sail := rfl
  have hrs2_s2 : rX_bits rs2 s2.sail = .ok divisor s2.sail := by
    rw [hs2_sail]; exact hrs2
  have hguard_s2 : ¬ (divisor = 0#64 ∧ s2.vregs a2VReg ≠ (-1 : BitVec 64)) := by
    rw [hs2_v0]; exact hguard_div0
  have h3 : (JoltISA.execInstr (.VirtualAssertValidDiv0 rs2 a2VReg)).run s2 =
      .ok RETIRE_SUCCESS s2 :=
    vreg_assert_valid_div0_run_ok rs2 a2VReg s2 divisor hrs2_s2 hguard_s2
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s2 h3]
  rfl

/-- Phase 2 — adjusted divisor + MUL/MULH + overflow-check assert.

The `hguard_overflow` hypothesis has the shape produced by
`v3_eq_v5_of_honest` (in `Div_math.lean`): `mulhs q adj = (q*adj).sshiftRight 63`. -/
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
      (JoltISA.execProgram (phase_overflow_check rs1 rs2)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.vregs a3VReg = rem ∧
      js'.vregs t0VReg = adj ∧
      js'.vregs t2VReg = q * adj ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  -- Step 1: vreg_change_divisor 2 rs1 rs2 → writes adj_value to v2; s1 opaque.
  obtain ⟨s1, h1, h1_v2, h1_pres, h1_sail⟩ :=
    vreg_change_divisor_run_ex t0VReg rs1 rs2 js dividend divisor hrs1 hrs2 (by unfold WritableVReg; decide)
  -- Step 2: lowered MULH block → writes mulhs(s1.v0, s1.v2) to v3.
  obtain ⟨s2, h2_sail, h2_v0, h2_v1, h2_v2, h2_v3, h2_run⟩ :=
    JoltISA.exists_state_after_div_rem_mulh_block_run s1
  -- Step 3: vreg_MUL 7 0 2 → writes (s2.v0 * s2.v2) to v7; s3 opaque.
  obtain ⟨s3, h3, h3_v7, h3_pres, h3_sail⟩ := vreg_MUL_run_ex t2VReg a2VReg t0VReg s2 (by unfold WritableVReg; decide)
  -- Step 4: lowered SRAI block 8 7 63 → writes (s3.v7).sshiftRight 63 to v8.
  obtain ⟨s4, h4, h4_v8, h4_pres, h4_sail⟩ := vreg_SRAI_run_ex t3VReg t2VReg 63 s3 (by unfold WritableVReg; decide)
  -- Lookups on s1 (chained from js).
  have hs1_v0 : s1.vregs a2VReg = q := (h1_pres a2VReg (by decide)).trans h_v0
  have hs1_v2 : s1.vregs t0VReg = adj := h1_v2.trans hadj.symm
  -- Lookups on s2 after the lowered MULH block.
  have hs2_v0 : s2.vregs a2VReg = q := h2_v0.trans hs1_v0
  have hs2_v1 : s2.vregs a3VReg = rem := h2_v1.trans ((h1_pres a3VReg (by decide)).trans h_v1)
  have hs2_v2 : s2.vregs t0VReg = adj := h2_v2.trans hs1_v2
  have hs2_v3 : s2.vregs t1VReg = mulhs q adj := by rw [h2_v3, hs1_v0, hs1_v2]
  -- Lookups on s3 (h3_pres preserves v3, h3_v7 specialises v7).
  have hs3_v3 : s3.vregs t1VReg = mulhs q adj := (h3_pres t1VReg (by decide)).trans hs2_v3
  have hs3_v7 : s3.vregs t2VReg = q * adj := by rw [h3_v7, hs2_v0, hs2_v2]
  -- Lookups on s4 needed for the assert and post-condition.
  have hs4_v3 : s4.vregs t1VReg = mulhs q adj := (h4_pres t1VReg (by decide)).trans hs3_v3
  have hs4_v8 : s4.vregs t3VReg = (q * adj).sshiftRight 63 := by
    rw [h4_v8, hs3_v7]; rfl
  -- Step 5: assert v3 = v8 — discharged via the overflow guard.
  have hguard_eq : s4.vregs t1VReg = s4.vregs t3VReg := by
    rw [hs4_v3, hs4_v8]; exact hguard_overflow
  have h5 : (JoltISA.execInstr (.VirtualAssertEQ t1VReg t3VReg)).run s4 =
      .ok RETIRE_SUCCESS s4 :=
    vreg_assert_eq_run_ok t1VReg t3VReg s4 hguard_eq
  -- Post-condition vregs lookups on s4.
  have hs4_v0 : s4.vregs a2VReg = q :=
    ((h4_pres a2VReg (by decide)).trans (h3_pres a2VReg (by decide))).trans hs2_v0
  have hs4_v1 : s4.vregs a3VReg = rem :=
    ((h4_pres a3VReg (by decide)).trans (h3_pres a3VReg (by decide))).trans hs2_v1
  have hs4_v2 : s4.vregs t0VReg = adj :=
    ((h4_pres t0VReg (by decide)).trans (h3_pres t0VReg (by decide))).trans hs2_v2
  have hs4_v7 : s4.vregs t2VReg = q * adj := (h4_pres t2VReg (by decide)).trans hs3_v7
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  -- Stitch the instruction chain.
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_v7, hs4_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [h2_run _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [h4 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s4 h5]
  rfl
/-- Phase 3 — signed-remainder reconstruction + `assert_eq_real v4 rs1`.

`signed_rem` is `(rem XOR sign(dividend)) - sign(dividend)` — the
two's-complement sign-fixup of `|r|` to its signed form. The guard
`hguard_quotient_product` says `q*adj + signed_rem = dividend`, i.e.
the division equation reconstructs the dividend. -/
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
      js'.sail = js.sail := by
  unfold phase_quotient_product
  -- Step 1: vreg_SRAI_from_real 3 rs1 63 → writes sshiftRight dividend 63 to v3.
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ :=
    vreg_SRAI_from_real_run_ex t1VReg rs1 63 js dividend hrs1 (by unfold WritableVReg; decide)
  -- Step 2: vreg_XOR 8 1 3 → writes (s1.v1 ^^^ s1.v3) to v8.
  obtain ⟨s2, h2, h2_v8, h2_pres, h2_sail⟩ := vreg_XOR_run_ex t3VReg a3VReg t1VReg s1 (by unfold WritableVReg; decide)
  -- Step 3: vreg_SUB 8 8 3 → writes (s2.v8 - s2.v3) to v8.
  obtain ⟨s3, h3, h3_v8, h3_pres, h3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t1VReg s2 (by unfold WritableVReg; decide)
  -- Step 4: vreg_ADD 7 7 8 → writes (s3.v7 + s3.v8) to v7.
  obtain ⟨s4, h4, h4_v7, h4_pres, h4_sail⟩ := vreg_ADD_run_ex t2VReg t2VReg t3VReg s3 (by unfold WritableVReg; decide)
  -- Sail propagation.
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  -- Lookups on s1.
  have hs1_v1 : s1.vregs a3VReg = rem := (h1_pres a3VReg (by decide)).trans h_v1
  have hs1_v3 : s1.vregs t1VReg = dividend.sshiftRight 63 := by rw [h1_v3]; rfl
  have hs1_v7 : s1.vregs t2VReg = q * adj := (h1_pres t2VReg (by decide)).trans h_v7
  -- Lookups on s2.
  have hs2_v3 : s2.vregs t1VReg = dividend.sshiftRight 63 :=
    (h2_pres t1VReg (by decide)).trans hs1_v3
  have hs2_v7 : s2.vregs t2VReg = q * adj := (h2_pres t2VReg (by decide)).trans hs1_v7
  have hs2_v8 : s2.vregs t3VReg = rem ^^^ dividend.sshiftRight 63 := by
    rw [h2_v8, hs1_v1, hs1_v3]
  -- Lookups on s3.
  have hs3_v7 : s3.vregs t2VReg = q * adj := (h3_pres t2VReg (by decide)).trans hs2_v7
  have hs3_v8 :
      s3.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [h3_v8, hs2_v8, hs2_v3]
  -- Lookup on s4: v7 derivation for the assert.
  have hs4_v7 : s4.vregs t2VReg = dividend := by
    rw [h4_v7, hs3_v7, hs3_v8]; exact hguard_quotient_product
  -- Step 5: assert v7 = rs1 — discharged via hguard_quotient_product.
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail := hs4_sail.symm ▸ hrs1
  have h5 : (JoltISA.execInstr (.VirtualAssertEQReal t2VReg rs1)).run s4 =
      .ok RETIRE_SUCCESS s4 :=
    vreg_assert_eq_real_run_ok t2VReg rs1 s4 dividend hrs1_s4 hs4_v7
  -- Post-condition vregs lookups: v0/v1/v2 all preserved through writes {3, 8, 8, 7}.
  have hs4_v0 : s4.vregs a2VReg = q :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres a2VReg (by decide)).trans h_v0
  have hs4_v1 : s4.vregs a3VReg = rem :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres a3VReg (by decide)).trans h_v1
  have hs4_v2 : s4.vregs t0VReg = adj :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres t0VReg (by decide)).trans h_v2
  -- Stitch the instruction chain.
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_sail⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s4 h4]
  rw [JoltISA.execProgram_instr_run_retire _ _ s4 s4 h5]
  rfl

/-- Phase 4 — compute |adj| + `assert_valid_unsigned_remainder v1 v5`.

Guard: `|adj| = 0 ∨ rem.toNat < |adj|.toNat` — either the adjusted
divisor is zero (which makes the assert vacuous, matching the Rust
short-circuit on divisor = 0), or the absolute remainder is strictly
less than the absolute adjusted divisor, unsigned. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs a2VReg = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  -- Step 1: vreg_SRAI 3 2 63 → writes shift_bits_right_arith (s.v2) 63 to v3.
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ := vreg_SRAI_run_ex t1VReg t0VReg 63 js (by unfold WritableVReg; decide)
  -- Step 2: vreg_XOR 8 2 3 → writes (s1.v2 ^^^ s1.v3) to v8.
  obtain ⟨s2, h2, h2_v8, h2_pres, h2_sail⟩ := vreg_XOR_run_ex t3VReg t0VReg t1VReg s1 (by unfold WritableVReg; decide)
  -- Step 3: vreg_SUB 8 8 3 → writes (s2.v8 - s2.v3) to v8.
  obtain ⟨s3, h3, h3_v8, h3_pres, h3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t1VReg s2 (by unfold WritableVReg; decide)
  -- Sail propagation.
  have hs3_sail : s3.sail = js.sail := h3_sail.trans (h2_sail.trans h1_sail)
  -- Lookups on s1.
  have hs1_v2 : s1.vregs t0VReg = adj := (h1_pres t0VReg (by decide)).trans h_v2
  have hs1_v3 : s1.vregs t1VReg = adj.sshiftRight 63 := by rw [h1_v3, h_v2]; rfl
  -- Lookups on s2.
  have hs2_v3 : s2.vregs t1VReg = adj.sshiftRight 63 :=
    (h2_pres t1VReg (by decide)).trans hs1_v3
  have hs2_v8 : s2.vregs t3VReg = adj ^^^ adj.sshiftRight 63 := by
    rw [h2_v8, hs1_v2, hs1_v3]
  -- Lookups on s3 — for the assert.
  have hs3_v8 : s3.vregs t3VReg = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [h3_v8, hs2_v8, hs2_v3]
  have hs3_v1 : s3.vregs a3VReg = rem :=
    (chain_pres_3 h1_pres h2_pres h3_pres a3VReg (by decide)).trans h_v1
  -- Step 4: assert v1 < v8 — discharged via hguard_rem_bound.
  have hguard_lt : s3.vregs t3VReg = 0#64 ∨ (s3.vregs a3VReg).toNat < (s3.vregs t3VReg).toNat := by
    rw [hs3_v1, hs3_v8]; exact hguard_rem_bound
  have h4 : (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder a3VReg t3VReg)).run s3
              = .ok RETIRE_SUCCESS s3 :=
    vreg_assert_valid_unsigned_remainder_run_ok a3VReg t3VReg s3 hguard_lt
  -- Post-condition: v0 preserved through all 3 writes.
  have hs3_v0 : s3.vregs a2VReg = q :=
    (chain_pres_3 h1_pres h2_pres h3_pres a2VReg (by decide)).trans h_v0
  -- Stitch the instruction chain.
  refine ⟨s3, ?_, hs3_v0, hs3_sail⟩
  rw [h1 _]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

/-- Phase 5 — writeback `rd := v0`. Writes the quotient to real `rd`
via `liftSail (wX_bits rd q)`; produces `sail = stateAfterWrite js.sail rd q`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback
  have hq : js.vregs a2VReg + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have hrun := vreg_ADDI_to_real_run rd a2VReg 0 js s' (by rw [hq]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd q
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction)
-- ----------------------------------------------------------------------------
-- Each of these takes `(JoltISA.execProgram phase_*).run js =
-- .ok RETIRE_SUCCESS js₁` and extracts the
-- guard that the assert inside the phase enforced, plus the same state
-- invariants the forward version establishes. Used by `divProgram_sound`.

/-- Phase 1 soundness — if `phase_setup` ok-terminates, the div0 guard
must have held and the advice landed in `v0`, `v1` without disturbing
`.sail`. -/
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
  unfold phase_setup at hp
  -- Step 1: unpeel `VirtualAdvice 0 q`.
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, hs1_pres, hs1_sail⟩ := vreg_advice_run_ex a2VReg q js (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: unpeel `VirtualAdvice 1 rem`.
  obtain ⟨s₂, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₂, hrun2_ex, hs2_v1, hs2_pres, hs2_sail⟩ := vreg_advice_run_ex a3VReg rem s₁ (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨js_afterAssert, hrun3, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  -- Step 3: assert. Cross-state lookups for the guard.
  have hs2_v0 : s₂.vregs a2VReg = q := (hs2_pres a2VReg (by decide)).trans hs1_v0
  have hs2_sail_orig : s₂.sail = js.sail := hs2_sail.trans hs1_sail
  have hrs2_s2 : rX_bits rs2 s₂.sail = .ok divisor s₂.sail := hs2_sail_orig.symm ▸ hrs2
  -- Case-split on the div0 guard via the assert's _run_ok / _run_err.
  by_cases hguard : (divisor = 0#64 ∧ s₂.vregs a2VReg ≠ (-1 : BitVec 64))
  · -- guard fires → throw, contradicts .ok
    exfalso
    have herr := vreg_assert_valid_div0_run_err rs2 a2VReg s₂ divisor hrs2_s2 hguard
    rw [herr] at hrun3
    cases hrun3
  · -- guard holds → state preserved, js₁ = s₂
    have hok := vreg_assert_valid_div0_run_ok rs2 a2VReg s₂ divisor hrs2_s2 hguard
    rw [hok] at hrun3
    cases hrun3
    refine ⟨?_, hs2_v0, hs2_v1, hs2_sail_orig⟩
    rw [hs2_v0] at hguard
    exact hguard

/-- Phase 2 soundness — if `phase_overflow_check` ok-terminates given
the standing invariants on `js`, the overflow-check assert's guard
held, and `v2`/`v4` now hold `adj`/`q·adj`. -/
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
  unfold phase_overflow_check at hp
  -- Step 1: vreg_change_divisor 2 rs1 rs2.
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v2, hs1_pres, hs1_sail⟩ :=
    vreg_change_divisor_run_ex t0VReg rs1 rs2 js dividend divisor hrs1 hrs2 (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: lowered MULH block 3 0 2.
  obtain ⟨s₂, hs2_sail, hs2_v0, hs2_v1, hs2_v2, hs2_v3, hrun2_ex⟩ :=
    JoltISA.exists_state_after_div_rem_mulh_block_run s₁
  rw [hrun2_ex _] at hp
  -- Step 3: vreg_MUL 7 0 2.
  obtain ⟨s₃, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₃, hrun3_ex, hs3_v7, hs3_pres, hs3_sail⟩ := vreg_MUL_run_ex t2VReg a2VReg t0VReg s₂ (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  -- Step 4: lowered SRAI block 8 7 63.
  obtain ⟨s₄, hrun4_ex, hs4_v8, hs4_pres, hs4_sail⟩ := vreg_SRAI_run_ex t3VReg t2VReg 63 s₃ (by unfold WritableVReg; decide)
  rw [hrun4_ex _] at hp
  obtain ⟨js_afterAssert, hrun5, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  -- Cross-state lookups (chained through preservation).
  have hs1_v0 : s₁.vregs a2VReg = q := (hs1_pres a2VReg (by decide)).trans h_v0
  have hs1_v2_adj : s₁.vregs t0VReg = adj := hs1_v2.trans hadj.symm
  have hs2_v0' : s₂.vregs a2VReg = q := hs2_v0.trans hs1_v0
  have hs2_v1' : s₂.vregs a3VReg = rem := hs2_v1.trans ((hs1_pres a3VReg (by decide)).trans h_v1)
  have hs2_v2' : s₂.vregs t0VReg = adj := hs2_v2.trans hs1_v2_adj
  have hs2_v3' : s₂.vregs t1VReg = mulhs q adj := by rw [hs2_v3, hs1_v0, hs1_v2_adj]
  have hs3_v3 : s₃.vregs t1VReg = mulhs q adj := (hs3_pres t1VReg (by decide)).trans hs2_v3'
  have hs3_v7' : s₃.vregs t2VReg = q * adj := by rw [hs3_v7, hs2_v0', hs2_v2']
  have hs4_v3 : s₄.vregs t1VReg = mulhs q adj := (hs4_pres t1VReg (by decide)).trans hs3_v3
  have hs4_v8' : s₄.vregs t3VReg = (q * adj).sshiftRight 63 := by
    rw [hs4_v8, hs3_v7']; rfl
  -- Step 5: assert v3 = v8. Case-split on the equality guard.
  by_cases hguard_eq : s₄.vregs t1VReg = s₄.vregs t3VReg
  · -- Derive all post-state facts BEFORE the assert's `cases hp`, since that
    -- substitutes `s₄ → js₁` and dismisses references to `s₄`.
    have hguard : mulhs q adj = (q * adj).sshiftRight 63 := by
      rw [← hs4_v3, hguard_eq, hs4_v8']
    have hs4_v0 : s₄.vregs a2VReg = q :=
      ((hs4_pres a2VReg (by decide)).trans (hs3_pres a2VReg (by decide))).trans hs2_v0'
    have hs4_v1 : s₄.vregs a3VReg = rem :=
      ((hs4_pres a3VReg (by decide)).trans (hs3_pres a3VReg (by decide))).trans hs2_v1'
    have hs4_v2 : s₄.vregs t0VReg = adj :=
      ((hs4_pres t0VReg (by decide)).trans (hs3_pres t0VReg (by decide))).trans hs2_v2'
    have hs4_v7 : s₄.vregs t2VReg = q * adj := (hs4_pres t2VReg (by decide)).trans hs3_v7'
    have hs4_sail_orig : s₄.sail = js.sail :=
      hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
    have hok := vreg_assert_eq_run_ok t1VReg t3VReg s₄ hguard_eq
    rw [hok] at hrun5
    cases hrun5
    exact ⟨hguard, hs4_v0, hs4_v1, hs4_v2, hs4_v7, hs4_sail_orig⟩
  · -- guard fails → throw, contradicts .ok
    exfalso
    have herr := vreg_assert_eq_run_err t1VReg t3VReg s₄ hguard_eq
    rw [herr] at hrun5
    cases hrun5

/-- Phase 3 soundness — if `phase_quotient_product` ok-terminates, the
division equation `q·adj + signed_rem = dividend` held. -/
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
  js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  -- Step 1: vreg_SRAI_from_real 3 rs1 63.
  obtain ⟨s₁, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ :=
    vreg_SRAI_from_real_run_ex t1VReg rs1 63 js dividend hrs1 (by unfold WritableVReg; decide)
  rw [hrun1_ex _] at hp
  -- Step 2: vreg_XOR 8 1 3.
  obtain ⟨s₂, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₂, hrun2_ex, hs2_v8, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t3VReg a3VReg t1VReg s₁ (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: vreg_SUB 8 8 3.
  obtain ⟨s₃, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₃, hrun3_ex, hs3_v8, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t1VReg s₂ (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  -- Step 4: vreg_ADD 7 7 8.
  obtain ⟨s₄, hrun4, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₄, hrun4_ex, hs4_v7, hs4_pres, hs4_sail⟩ := vreg_ADD_run_ex t2VReg t2VReg t3VReg s₃ (by unfold WritableVReg; decide)
  rw [hrun4_ex] at hrun4
  cases hrun4
  obtain ⟨js_afterAssert, hrun5, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  -- Cross-state lookups for the v7 derivation.
  have hs1_v1 : s₁.vregs a3VReg = rem := (hs1_pres a3VReg (by decide)).trans h_v1
  have hs1_v3' : s₁.vregs t1VReg = dividend.sshiftRight 63 := by rw [hs1_v3]; rfl
  have hs1_v7 : s₁.vregs t2VReg = q * adj := (hs1_pres t2VReg (by decide)).trans h_v7
  have hs2_v3 : s₂.vregs t1VReg = dividend.sshiftRight 63 :=
    (hs2_pres t1VReg (by decide)).trans hs1_v3'
  have hs2_v7 : s₂.vregs t2VReg = q * adj := (hs2_pres t2VReg (by decide)).trans hs1_v7
  have hs2_v8' : s₂.vregs t3VReg = rem ^^^ dividend.sshiftRight 63 := by
    rw [hs2_v8, hs1_v1, hs1_v3']
  have hs3_v7 : s₃.vregs t2VReg = q * adj := (hs3_pres t2VReg (by decide)).trans hs2_v7
  have hs3_v8' :
      s₃.vregs t3VReg = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [hs3_v8, hs2_v8', hs2_v3]
  have hs4_v7' :
      s₄.vregs t2VReg =
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) := by
    rw [hs4_v7, hs3_v7, hs3_v8']
  -- Sail propagation, transport hrs1 to s₄.
  have hs4_sail_orig : s₄.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  have hrs1_s4 : rX_bits rs1 s₄.sail = .ok dividend s₄.sail :=
    hs4_sail_orig.symm ▸ hrs1
  -- Step 5: assert v7 = rs1. Case-split on guard.
  by_cases hguard : s₄.vregs t2VReg = dividend
  · have hok := vreg_assert_eq_real_run_ok t2VReg rs1 s₄ dividend hrs1_s4 hguard
    rw [hok] at hrun5
    cases hrun5
    refine ⟨?_, ?_, ?_, ?_, hs4_sail_orig⟩
    · rw [← hs4_v7']; exact hguard
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres a2VReg (by decide)).trans h_v0
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres a3VReg (by decide)).trans h_v1
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres t0VReg (by decide)).trans h_v2
  · exfalso
    have herr := vreg_assert_eq_real_run_err t2VReg rs1 s₄ dividend hrs1_s4 hguard
    rw [herr] at hrun5
    cases hrun5

/-- Phase 4 soundness — if `phase_remainder_bound` ok-terminates, the
unsigned remainder bound holds *or* the adjusted divisor is zero (the
Rust assert short-circuits in that case). -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_v1 : js.vregs a3VReg = rem)
    (h_v2 : js.vregs t0VReg = adj)
    (hp : (JoltISA.execProgram phase_remainder_bound).run js =
      .ok RETIRE_SUCCESS js₁) :
    (((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) ∧
    js₁.vregs a2VReg = q ∧
  js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  -- Step 1: vreg_SRAI 3 2 63.
  obtain ⟨s₁, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex t1VReg t0VReg 63 js (by unfold WritableVReg; decide)
  rw [hrun1_ex _] at hp
  -- Step 2: vreg_XOR 8 2 3.
  obtain ⟨s₂, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₂, hrun2_ex, hs2_v8, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex t3VReg t0VReg t1VReg s₁ (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: vreg_SUB 8 8 3.
  obtain ⟨s₃, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₃, hrun3_ex, hs3_v8, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex t3VReg t3VReg t1VReg s₂ (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  obtain ⟨js_afterAssert, hrun4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  -- Cross-state lookups for the v8 derivation = |adj|.
  have hs1_v2 : s₁.vregs t0VReg = adj := (hs1_pres t0VReg (by decide)).trans h_v2
  have hs1_v3' : s₁.vregs t1VReg = adj.sshiftRight 63 := by rw [hs1_v3, h_v2]; rfl
  have hs2_v3 : s₂.vregs t1VReg = adj.sshiftRight 63 :=
    (hs2_pres t1VReg (by decide)).trans hs1_v3'
  have hs2_v8' : s₂.vregs t3VReg = adj ^^^ adj.sshiftRight 63 := by
    rw [hs2_v8, hs1_v2, hs1_v3']
  have hs3_v8' :
      s₃.vregs t3VReg = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [hs3_v8, hs2_v8', hs2_v3]
  have hs3_v1 : s₃.vregs a3VReg = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres a3VReg (by decide)).trans h_v1
  have hs3_sail_orig : s₃.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  -- Step 4: assert (v8 = 0 ∨ v1 < v8). Case-split on guard.
  by_cases hguard : s₃.vregs t3VReg = 0#64 ∨ (s₃.vregs a3VReg).toNat < (s₃.vregs t3VReg).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok a3VReg t3VReg s₃ hguard
    rw [hok] at hrun4
    cases hrun4
    refine ⟨?_, ?_, hs3_sail_orig⟩
    · rcases hguard with h0 | hlt
      · left; rw [← hs3_v8']; exact h0
      · right; rw [← hs3_v1, ← hs3_v8']; exact hlt
    · exact (chain_pres_3 hs1_pres hs2_pres hs3_pres a2VReg (by decide)).trans h_v0
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err a3VReg t3VReg s₃ hguard
    rw [herr] at hrun4
    cases hrun4

/-- Phase 5 soundness — writeback is unconditional; just characterises
the final state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs a2VReg = q)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hq : js.vregs a2VReg + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg a2VReg) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd a2VReg 0 js s' (by rw [hq]; exact hw)
  rw [hp_concrete] at hrun
  cases hrun
  show s' = stateAfterWrite js_ref rd q
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

end Div

end
