import JoltBytecode.InstructionEquivalence.ProofSupport
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Primitives

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Phase decomposition and run helpers for `jolt_div`

The 18 steps of `jolt_div` split into five phases, each one ending at
(or dominated by) an assertion. This file holds:

* the **phase definitions** (pure monadic programs, each a 1–5 step
  sub-sequence of `jolt_div`),
* the **bind-peel helper** `bind_run_of_ok` used to chain phases
  together,
* the **phase-run lemmas** — one per phase — characterising what each
  phase produces given its preconditions and guards.

All phase-run lemmas are sorried for now; each will be discharged by
unfolding its phase into the raw bind chain and walking it with
`bind_run_of_ok`, using the per-primitive `_run`/`_run_ok` lemmas +
the supplied guard hypothesis.
-/

-- ----------------------------------------------------------------------------
-- Phase definitions
-- ----------------------------------------------------------------------------

/-- Phase 1 — advice loads + div-by-zero assert. -/
def phase_setup (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient
  let _ ← vreg_advice 1 rem_abs
  vreg_assert_valid_div0 rs2 0

/-- Phase 2 — adjusted divisor, MULH/MUL/SRAI, overflow-check assert. -/
def phase_overflow_check (rs1 rs2 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_change_divisor 2 rs1 rs2
  let _ ← vreg_MULH 3 0 2
  let _ ← vreg_MUL 4 0 2
  let _ ← vreg_SRAI 5 4 63
  vreg_assert_eq 3 5

/-- Phase 3 — reconstruct signed remainder, sum, assert equals dividend. -/
def phase_quotient_product (rs1 : regidx) : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI_from_real 3 rs1 63
  let _ ← vreg_XOR 5 1 3
  let _ ← vreg_SUB 5 5 3
  let _ ← vreg_ADD 4 4 5
  vreg_assert_eq_real 4 rs1

/-- Phase 4 — compute |adj_div|, assert |r| < |adj_div|. -/
def phase_remainder_bound : JoltMonad ExecutionResult := do
  let _ ← vreg_SRAI 3 2 63
  let _ ← vreg_XOR 5 2 3
  let _ ← vreg_SUB 5 5 3
  vreg_assert_valid_unsigned_remainder 1 5

/-- Phase 5 — move the quotient advice from v0 into real register rd. -/
def phase_writeback (rd : regidx) : JoltMonad ExecutionResult :=
  vreg_ADDI_to_real rd 0 0

-- ----------------------------------------------------------------------------
-- Bind-peel helper
-- ----------------------------------------------------------------------------

/-- Bind-peel: if `m` runs to `.ok a js₁`, the whole chain
`(m >>= f).run js` reduces to `(f a).run js₁`. -/
theorem bind_run_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js₁ : SailJoltState} {a : α}
    (h : m.run js = .ok a js₁) :
    (m >>= f).run js = (f a).run js₁ := by
  show (m >>= f) js = (f a) js₁
  simp only [bind, EStateM.bind]
  rw [show m js = .ok a js₁ from h]

/-- Bind-unpeel: if `(m >>= f).run js` ok-terminates, then there must
have been an intermediate `(a, js₁)` produced by `m`, and the tail
`f a` takes `js₁` to the same final state. Reverse direction of
`bind_run_of_ok`; the existential is forced because the intermediate
state is not visible in the compound hypothesis. Used by soundness-
style proofs that tear a chain apart from the outside in. -/
theorem bind_unpeel_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js' : SailJoltState} {b : β}
    (h : (m >>= f).run js = .ok b js') :
    ∃ (a : α) (js₁ : SailJoltState),
      m.run js = .ok a js₁ ∧ (f a).run js₁ = .ok b js' := by
  cases hmj : m.run js with
  | ok a js₁ =>
    refine ⟨a, js₁, rfl, ?_⟩
    have hpeel : (m >>= f).run js = (f a).run js₁ := bind_run_of_ok hmj
    rw [hpeel] at h
    exact h
  | error e js₁ =>
    exfalso
    have herr : (m >>= f).run js = .error e js₁ := by
      show (m >>= f) js = .error e js₁
      simp only [bind, EStateM.bind]
      rw [show m js = .error e js₁ from hmj]
    rw [herr] at h
    cases h

-- ============================================================================
-- Vregs-after-write helpers
-- ============================================================================
/-!
Looking up a vreg index `k` on a state of the form
`{ sail := …, vregs := fun r => if r = vd then v else js.vregs r }`
(the shape every per-instruction `_run` lemma produces) is either `v`
(when `k = vd`) or `js.vregs k` (when `k ≠ vd`). These two helpers let
phase proofs discharge each cross-state lookup in one line via
`vregs_write_self` / `vregs_write_pres`, instead of the 3+ line
`show … rw [if_pos|if_neg] …` chain inline.
-/

/-- After writing `v` to vreg `vd`, the lookup at `vd` returns `v`. -/
theorem vregs_write_self (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs vd
      = v := by
  show (if vd = vd then v else js.vregs vd) = v
  rw [if_pos rfl]

/-- After writing `v` to vreg `vd`, the lookup at any other index `k`
returns the original value `js.vregs k`. -/
theorem vregs_write_pres (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64)
    (k : BitVec 7) (h : k ≠ vd) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs k
      = js.vregs k := by
  show (if k = vd then v else js.vregs k) = js.vregs k
  rw [if_neg h]

/-- Chain four preservation hypotheses: if `k` differs from each of the four
write destinations, the vregs lookup is preserved through all four writes. -/
theorem chain_pres_4 {s_a s_b s_c s_d s_e : SailJoltState}
    {vd_a vd_b vd_c vd_d : BitVec 7}
    (h_a : ∀ k, k ≠ vd_a → s_b.vregs k = s_a.vregs k)
    (h_b : ∀ k, k ≠ vd_b → s_c.vregs k = s_b.vregs k)
    (h_c : ∀ k, k ≠ vd_c → s_d.vregs k = s_c.vregs k)
    (h_d : ∀ k, k ≠ vd_d → s_e.vregs k = s_d.vregs k)
    (k : BitVec 7)
    (h_k : k ≠ vd_a ∧ k ≠ vd_b ∧ k ≠ vd_c ∧ k ≠ vd_d) :
    s_e.vregs k = s_a.vregs k := by
  obtain ⟨h_k_a, h_k_b, h_k_c, h_k_d⟩ := h_k
  exact (((h_d k h_k_d).trans (h_c k h_k_c)).trans (h_b k h_k_b)).trans (h_a k h_k_a)

/-- Chain three preservation hypotheses (Phase 4 has only three writes). -/
theorem chain_pres_3 {s_a s_b s_c s_d : SailJoltState}
    {vd_a vd_b vd_c : BitVec 7}
    (h_a : ∀ k, k ≠ vd_a → s_b.vregs k = s_a.vregs k)
    (h_b : ∀ k, k ≠ vd_b → s_c.vregs k = s_b.vregs k)
    (h_c : ∀ k, k ≠ vd_c → s_d.vregs k = s_c.vregs k)
    (k : BitVec 7)
    (h_k : k ≠ vd_a ∧ k ≠ vd_b ∧ k ≠ vd_c) :
    s_d.vregs k = s_a.vregs k := by
  obtain ⟨h_k_a, h_k_b, h_k_c⟩ := h_k
  exact ((h_c k h_k_c).trans (h_b k h_k_b)).trans (h_a k h_k_a)

-- ============================================================================
-- Per-instruction `_run` lemmas (scaffolding for the phase helpers)
-- ============================================================================
/-!
Below are the per-instruction characterisation lemmas needed to close
the phase-run helpers (`phase_setup_run`, `phase_overflow_check_run`,
`phase_quotient_product_run`, `phase_remainder_bound_run`,
`phase_writeback_run`) and their soundness duals.

Each pure arithmetic op gets a single `_run` lemma. Each Sail-touching
op (`vreg_change_divisor`, `vreg_SRAI_from_real`, `vreg_ADDI_to_real`)
takes the relevant `rX_bits`/`wX_bits` outcome as a hypothesis. Each
assert gets a paired `_run_ok` / `_run_err` — mirroring
`divYbyX_run_ok` / `divYbyX_run_err` from the toy — so callers feed
`bind_run_of_ok` a clean equation rather than an `if`.

`vreg_XOR_run` is already proved in `VirtualInstructions.lean` and is
not restated here.

Once these are filled in, each phase helper closes mechanically:

  1. `let s_i : SailJoltState := …` for each intermediate state.
  2. `have h_i : <instr>.run s_{i-1} = .ok _ s_i := <instr>_run …` per step.
  3. `unfold phase_*; rw [bind_run_of_ok h_1]; …; exact h_n`.

Soundness analogues run `bind_unpeel_of_ok` in the opposite direction
and use `_run_err` to rule out the throw arm of each assert.
-/

-- ----------------------------------------------------------------------------
-- Pure-arithmetic ops (Phase 2/3/4 bodies)
-- ----------------------------------------------------------------------------

/-- `vreg_advice vd advice`: writes `advice` into virtual register `vd`,
leaving `sail` and all other vregs untouched. Never fails. -/
theorem vreg_advice_run (vd : BitVec 7) (advice : BitVec 64) (js : SailJoltState) :
    (vreg_advice vd advice).run js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then advice else js.vregs r } := by
  unfold vreg_advice
  simp only [bind, pure, writeVReg, modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- `vreg_MULH vd vs1 vs2`: writes `mulhs (js.vregs vs1) (js.vregs vs2)`
to `vd`. Pure. -/
theorem vreg_MULH_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_MULH vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then mulhs (js.vregs vs1) (js.vregs vs2)
                          else js.vregs r } := by
  unfold vreg_MULH
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- `vreg_MUL vd vs1 vs2`: writes the low 64 bits of the product to `vd`.
Pure. -/
theorem vreg_MUL_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_MUL vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 * js.vregs vs2
                          else js.vregs r } := by
  unfold vreg_MUL
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- `vreg_SRAI vd vs1 shamt`: arithmetic right shift of `vs1` by `shamt`,
written to `vd`. Pure. -/
theorem vreg_SRAI_run (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    vreg_SRAI vd vs1 shamt js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then shift_bits_right_arith (js.vregs vs1) shamt
                          else js.vregs r } := by
  unfold vreg_SRAI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- `vreg_ADD vd vs1 vs2`: 64-bit add. Pure. -/
theorem vreg_ADD_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_ADD vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 + js.vregs vs2
                          else js.vregs r } := by
  unfold vreg_ADD
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

/-- `vreg_SUB vd vs1 vs2`: 64-bit subtract. Pure. -/
theorem vreg_SUB_run (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    vreg_SUB vd vs1 vs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then js.vregs vs1 - js.vregs vs2
                          else js.vregs r } := by
  unfold vreg_SUB
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]

-- ----------------------------------------------------------------------------
-- Sail-touching ops (real-register reads/writes inside the phase bodies)
-- ----------------------------------------------------------------------------
-- Each of these takes an `rX_bits` or `wX_bits` hypothesis pinning down
-- the value read from / final state after writing to a real register.
-- The phase callers discharge that hypothesis from the standing
-- `hrs1`/`hrs2` arguments transported across the running `.sail` chain.

/-- `vreg_change_divisor vd rs1 rs2`: reads real `rs1` and `rs2`, writes
`change_divisor_value dividend divisor` to virtual register `vd`. -/
theorem vreg_change_divisor_run (vd : BitVec 7) (rs1 rs2 : regidx)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    vreg_change_divisor vd rs1 rs2 js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then change_divisor_value dividend divisor
          else js.vregs r } := by
  unfold vreg_change_divisor liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]
  simp only []
  rw [hrs2]

/-- `vreg_SRAI_from_real vd rs1 shamt`: reads real `rs1`, arithmetic
right shift by `shamt`, writes virtual `vd`. -/
theorem vreg_SRAI_from_real_run (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    vreg_SRAI_from_real vd rs1 shamt js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r =>
          if r = vd then shift_bits_right_arith rs1_val shamt
          else js.vregs r } := by
  unfold vreg_SRAI_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]

/-- `vreg_ADDI_to_real rd vs1 imm`: reads virtual `vs1`, adds the
sign-extended immediate, writes real `rd`. The post-write Sail state
`s'` is determined by `wX_bits rd (v + sext imm)` and threaded in from
the caller (`wX_shape` from `RegisterOps` produces the witness). -/
theorem vreg_ADDI_to_real_run (rd : regidx) (vs1 : BitVec 7) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (hwrite :
      wX_bits rd (js.vregs vs1 + sign_extend (m := 64) imm) js.sail
        = .ok () s') :
    vreg_ADDI_to_real rd vs1 imm js = .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } := by
  unfold vreg_ADDI_to_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hwrite]

-- ----------------------------------------------------------------------------
-- Asserts — paired `_run_ok` / `_run_err`
-- ----------------------------------------------------------------------------
-- Mirrors the `divYbyX_run_ok` / `divYbyX_run_err` split from the toy:
-- the success branch is what completeness chains through `bind_run_of_ok`;
-- the error branch is what soundness uses to contradict the throw arm
-- after an `_run_sound` unpeel produces a successful run.

/-- `vreg_assert_valid_div0 rs2 vq` — success branch. When the guard
`¬ (divisor = 0 ∧ vq ≠ -1)` holds, the assert passes through with no
state change. -/
theorem vreg_assert_valid_div0_run_ok (rs2 : regidx) (vq : BitVec 7)
    (js : SailJoltState) (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : ¬ (divisor = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64))) :
    vreg_assert_valid_div0 rs2 vq js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_valid_div0 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hrs2]
  simp only []
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_valid_div0 rs2 vq` — failure branch. When the guard
fires (`divisor = 0 ∧ vq ≠ -1`), the assert throws. -/
theorem vreg_assert_valid_div0_run_err (rs2 : regidx) (vq : BitVec 7)
    (js : SailJoltState) (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : divisor = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64)) :
    vreg_assert_valid_div0 rs2 vq js =
      .error
        (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1")
        js := by
  unfold vreg_assert_valid_div0 liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [hrs2]
  simp only []
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_eq va vb` — success branch. -/
theorem vreg_assert_eq_run_ok (va vb : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs va = js.vregs vb) :
    vreg_assert_eq va vb js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_eq
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_eq va vb` — failure branch. -/
theorem vreg_assert_eq_run_err (va vb : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs va ≠ js.vregs vb) :
    vreg_assert_eq va vb js =
      .error (Error.Assertion "VirtualAssertEQ") js := by
  unfold vreg_assert_eq
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_eq_real va rb` — success branch. The real-register
read is pinned by `hrb`; `hguard` says the virtual value matches. -/
theorem vreg_assert_eq_real_run_ok (va : BitVec 7) (rb : regidx)
    (js : SailJoltState) (rb_val : BitVec 64)
    (hrb : rX_bits rb js.sail = .ok rb_val js.sail)
    (hguard : js.vregs va = rb_val) :
    vreg_assert_eq_real va rb js = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_eq_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [hrb]
  simp only []
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_eq_real va rb` — failure branch. -/
theorem vreg_assert_eq_real_run_err (va : BitVec 7) (rb : regidx)
    (js : SailJoltState) (rb_val : BitVec 64)
    (hrb : rX_bits rb js.sail = .ok rb_val js.sail)
    (hguard : js.vregs va ≠ rb_val) :
    vreg_assert_eq_real va rb js =
      .error (Error.Assertion "VirtualAssertEQ (vreg vs real)") js := by
  unfold vreg_assert_eq_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [hrb]
  simp only []
  rw [if_neg hguard]
  rfl

/-- `vreg_assert_valid_unsigned_remainder vr vd` — success branch.
The guard is the disjunction `vd = 0 ∨ vr < vd` (matching the Rust
short-circuit on zero divisor). -/
theorem vreg_assert_valid_unsigned_remainder_run_ok
    (vr vd : BitVec 7) (js : SailJoltState)
    (hguard : js.vregs vd = 0#64 ∨ (js.vregs vr).toNat < (js.vregs vd).toNat) :
    vreg_assert_valid_unsigned_remainder vr vd js
      = .ok RETIRE_SUCCESS js := by
  unfold vreg_assert_valid_unsigned_remainder
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- `vreg_assert_valid_unsigned_remainder vr vd` — failure branch.
The throw fires precisely when `vd ≠ 0 ∧ vr ≥ vd`. -/
theorem vreg_assert_valid_unsigned_remainder_run_err
    (vr vd : BitVec 7) (js : SailJoltState)
    (hguard : ¬ (js.vregs vd = 0#64 ∨ (js.vregs vr).toNat < (js.vregs vd).toNat)) :
    vreg_assert_valid_unsigned_remainder vr vd js =
      .error
        (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0")
        js := by
  unfold vreg_assert_valid_unsigned_remainder
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, get, getThe, MonadStateOf.get, EStateM.get,
             throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  rw [if_neg hguard]
  rfl

-- ============================================================================
-- Existential `_run_ex` variants (opaque post-state)
-- ============================================================================
/-!
The concrete `_run` lemmas above expose the post-state's vregs as a
literal lambda `fun r => if r = vd then v else js.vregs r`. When several
vreg-writing instructions are chained, the inner `js.vregs r` references
the *previous* state's vregs, and the kernel has to walk the chain at
every cross-state lookup. With four or more chained writes, this hits
deep recursion.

The `_run_ex` variants below restate each writing instruction's effect
**propositionally** — `vregs vd = v`, vregs preserved at other indices,
sail preserved — and existentialise the post-state. After
`obtain ⟨s, h, h_at, h_pres, h_sail⟩ := vreg_X_run_ex …`, `s` is an
opaque fresh fvar; the kernel cannot unfold it, so no chain forms and
cross-state lookups become one-line consequences of `h_pres`.

Phase proofs that chain four or more vreg-writes (Phases 2–4) use these
variants. Phase 1 (only two writes) and Phase 5 (single sail write) keep
the concrete `_run` form. -/

/-- Existential variant of `vreg_advice_run`. -/
theorem vreg_advice_run_ex (vd : BitVec 7) (advice : BitVec 64) (js : SailJoltState) :
    ∃ js',
      (vreg_advice vd advice).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = advice ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_advice
  simp only [bind, pure, writeVReg, modify, modifyGet, MonadStateOf.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_MULH_run`. -/
theorem vreg_MULH_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_MULH vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = mulhs (js.vregs vs1) (js.vregs vs2) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_MULH
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_MUL_run`. -/
theorem vreg_MUL_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_MUL vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 * js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_MUL
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_SRAI_run`. -/
theorem vreg_SRAI_run_ex (vd vs1 : BitVec 7) (shamt : BitVec 6) (js : SailJoltState) :
    ∃ js',
      (vreg_SRAI vd vs1 shamt).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = shift_bits_right_arith (js.vregs vs1) shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_SRAI
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_change_divisor_run`. -/
theorem vreg_change_divisor_run_ex (vd : BitVec 7) (rs1 rs2 : regidx)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    ∃ js',
      (vreg_change_divisor vd rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = change_divisor_value dividend divisor ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_change_divisor vd rs1 rs2 js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_change_divisor liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]
  simp only []
  rw [hrs2]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_SRAI_from_real_run`. -/
theorem vreg_SRAI_from_real_run_ex (vd : BitVec 7) (rs1 : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (rs1_val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok rs1_val js.sail) :
    ∃ js',
      (vreg_SRAI_from_real vd rs1 shamt).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = shift_bits_right_arith rs1_val shamt ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  show ∃ js', vreg_SRAI_from_real vd rs1 shamt js = .ok RETIRE_SUCCESS js' ∧ _
  unfold vreg_SRAI_from_real liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             writeVReg, modify, modifyGet,
             MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [hrs1]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant for `vreg_XOR`. -/
theorem vreg_XOR_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_XOR vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 ^^^ js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_XOR
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_SUB_run`. -/
theorem vreg_SUB_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_SUB vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 - js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_SUB
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

/-- Existential variant of `vreg_ADD_run`. -/
theorem vreg_ADD_run_ex (vd vs1 vs2 : BitVec 7) (js : SailJoltState) :
    ∃ js',
      (vreg_ADD vd vs1 vs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = js.vregs vs1 + js.vregs vs2 ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  unfold vreg_ADD
  simp only [bind, EStateM.bind, pure, EStateM.pure,
             readVReg, writeVReg, get, modify, modifyGet,
             getThe, MonadStateOf.get, MonadStateOf.modifyGet,
             EStateM.get, EStateM.modifyGet]
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k h
    show (if k = vd then _ else js.vregs k) = _
    rw [if_neg h]

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
      (phase_setup rs2 q rem).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.sail = js.sail := by
  unfold phase_setup
  let s1 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = (0 : BitVec 7) then q else js.vregs r }
  let s2 : SailJoltState :=
    { sail := s1.sail
      vregs := fun r => if r = (1 : BitVec 7) then rem else s1.vregs r }
  have h1 : (vreg_advice 0 q).run js = .ok RETIRE_SUCCESS s1 := vreg_advice_run 0 q js
  have h2 : (vreg_advice 1 rem).run s1 = .ok RETIRE_SUCCESS s2 := vreg_advice_run 1 rem s1
  have hs2_v0 : s2.vregs 0 = q := by
    show (if (0 : BitVec 7) = 1 then rem else s1.vregs 0) = q
    rw [if_neg (by decide : (0 : BitVec 7) ≠ 1)]
    show (if (0 : BitVec 7) = 0 then q else js.vregs 0) = q
    rw [if_pos rfl]
  have hs2_v1 : s2.vregs 1 = rem := by
    show (if (1 : BitVec 7) = 1 then rem else s1.vregs 1) = rem
    rw [if_pos rfl]
  have hs2_sail : s2.sail = js.sail := rfl
  have hrs2_s2 : rX_bits rs2 s2.sail = .ok divisor s2.sail := by
    rw [hs2_sail]; exact hrs2
  have hguard_s2 : ¬ (divisor = 0#64 ∧ s2.vregs 0 ≠ (-1 : BitVec 64)) := by
    rw [hs2_v0]; exact hguard_div0
  have h3 : vreg_assert_valid_div0 rs2 0 s2 = .ok RETIRE_SUCCESS s2 :=
    vreg_assert_valid_div0_run_ok rs2 0 s2 divisor hrs2_s2 hguard_s2
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_sail⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2]
  exact h3

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
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hguard_overflow : mulhs q adj = (q * adj).sshiftRight 63) :
    ∃ js',
      (phase_overflow_check rs1 rs2).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.vregs 4 = q * adj ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  -- Step 1: vreg_change_divisor 2 rs1 rs2 → writes adj_value to v2; s1 opaque.
  obtain ⟨s1, h1, h1_v2, h1_pres, h1_sail⟩ :=
    vreg_change_divisor_run_ex 2 rs1 rs2 js dividend divisor hrs1 hrs2
  -- Step 2: vreg_MULH 3 0 2 → writes mulhs(s1.v0, s1.v2) to v3; s2 opaque.
  obtain ⟨s2, h2, h2_v3, h2_pres, h2_sail⟩ := vreg_MULH_run_ex 3 0 2 s1
  -- Step 3: vreg_MUL 4 0 2 → writes (s2.v0 * s2.v2) to v4; s3 opaque.
  obtain ⟨s3, h3, h3_v4, h3_pres, h3_sail⟩ := vreg_MUL_run_ex 4 0 2 s2
  -- Step 4: vreg_SRAI 5 4 63 → writes (s3.v4).sshiftRight 63 to v5; s4 opaque.
  obtain ⟨s4, h4, h4_v5, h4_pres, h4_sail⟩ := vreg_SRAI_run_ex 5 4 63 s3
  -- Lookups on s1 (chained from js).
  have hs1_v0 : s1.vregs 0 = q := (h1_pres 0 (by decide)).trans h_v0
  have hs1_v2 : s1.vregs 2 = adj := h1_v2.trans hadj.symm
  -- Lookups on s2 (chained through h2_pres, plus h2_v3 specialised).
  have hs2_v0 : s2.vregs 0 = q := (h2_pres 0 (by decide)).trans hs1_v0
  have hs2_v2 : s2.vregs 2 = adj := (h2_pres 2 (by decide)).trans hs1_v2
  have hs2_v3 : s2.vregs 3 = mulhs q adj := by rw [h2_v3, hs1_v0, hs1_v2]
  -- Lookups on s3 (h3_pres preserves v3, h3_v4 specialises v4).
  have hs3_v3 : s3.vregs 3 = mulhs q adj := (h3_pres 3 (by decide)).trans hs2_v3
  have hs3_v4 : s3.vregs 4 = q * adj := by rw [h3_v4, hs2_v0, hs2_v2]
  -- Lookups on s4 needed for the assert and post-condition.
  have hs4_v3 : s4.vregs 3 = mulhs q adj := (h4_pres 3 (by decide)).trans hs3_v3
  have hs4_v5 : s4.vregs 5 = (q * adj).sshiftRight 63 := by
    rw [h4_v5, hs3_v4]; rfl
  -- Step 5: assert v3 = v5 — discharged via the overflow guard.
  have hguard_eq : s4.vregs 3 = s4.vregs 5 := by
    rw [hs4_v3, hs4_v5]; exact hguard_overflow
  have h5 : (vreg_assert_eq 3 5).run s4 = .ok RETIRE_SUCCESS s4 :=
    vreg_assert_eq_run_ok 3 5 s4 hguard_eq
  -- Post-condition vregs lookups on s4: v0/v1 chain from js via combinator;
  -- v2 chains from s1 (after the v2 write) so manual 3-step .trans; v4 is one step.
  have hs4_v0 : s4.vregs 0 = q :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 0 (by decide)).trans h_v0
  have hs4_v1 : s4.vregs 1 = rem :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 1 (by decide)).trans h_v1
  have hs4_v2 : s4.vregs 2 = adj :=
    (((h4_pres 2 (by decide)).trans (h3_pres 2 (by decide))).trans
      (h2_pres 2 (by decide))).trans hs1_v2
  have hs4_v4 : s4.vregs 4 = q * adj := (h4_pres 4 (by decide)).trans hs3_v4
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  -- Stitch the bind chain.
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_v4, hs4_sail⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3, bind_run_of_ok h4]
  exact h5
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
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hguard_quotient_product :
        q * adj +
          ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
        = dividend) :
    ∃ js',
      (phase_quotient_product rs1).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.vregs 1 = rem ∧
      js'.vregs 2 = adj ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  -- Step 1: vreg_SRAI_from_real 3 rs1 63 → writes sshiftRight dividend 63 to v3.
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ :=
    vreg_SRAI_from_real_run_ex 3 rs1 63 js dividend hrs1
  -- Step 2: vreg_XOR 5 1 3 → writes (s1.v1 ^^^ s1.v3) to v5.
  obtain ⟨s2, h2, h2_v5, h2_pres, h2_sail⟩ := vreg_XOR_run_ex 5 1 3 s1
  -- Step 3: vreg_SUB 5 5 3 → writes (s2.v5 - s2.v3) to v5.
  obtain ⟨s3, h3, h3_v5, h3_pres, h3_sail⟩ := vreg_SUB_run_ex 5 5 3 s2
  -- Step 4: vreg_ADD 4 4 5 → writes (s3.v4 + s3.v5) to v4.
  obtain ⟨s4, h4, h4_v4, h4_pres, h4_sail⟩ := vreg_ADD_run_ex 4 4 5 s3
  -- Sail propagation.
  have hs4_sail : s4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  -- Lookups on s1.
  have hs1_v1 : s1.vregs 1 = rem := (h1_pres 1 (by decide)).trans h_v1
  have hs1_v3 : s1.vregs 3 = dividend.sshiftRight 63 := by rw [h1_v3]; rfl
  have hs1_v4 : s1.vregs 4 = q * adj := (h1_pres 4 (by decide)).trans h_v4
  -- Lookups on s2.
  have hs2_v3 : s2.vregs 3 = dividend.sshiftRight 63 :=
    (h2_pres 3 (by decide)).trans hs1_v3
  have hs2_v4 : s2.vregs 4 = q * adj := (h2_pres 4 (by decide)).trans hs1_v4
  have hs2_v5 : s2.vregs 5 = rem ^^^ dividend.sshiftRight 63 := by
    rw [h2_v5, hs1_v1, hs1_v3]
  -- Lookups on s3.
  have hs3_v4 : s3.vregs 4 = q * adj := (h3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5 :
      s3.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [h3_v5, hs2_v5, hs2_v3]
  -- Lookup on s4: v4 derivation for the assert.
  have hs4_v4 : s4.vregs 4 = dividend := by
    rw [h4_v4, hs3_v4, hs3_v5]; exact hguard_quotient_product
  -- Step 5: assert v4 = rs1 — discharged via hguard_quotient_product.
  have hrs1_s4 : rX_bits rs1 s4.sail = .ok dividend s4.sail := hs4_sail.symm ▸ hrs1
  have h5 : (vreg_assert_eq_real 4 rs1).run s4 = .ok RETIRE_SUCCESS s4 :=
    vreg_assert_eq_real_run_ok 4 rs1 s4 dividend hrs1_s4 hs4_v4
  -- Post-condition vregs lookups: v0/v1/v2 all preserved through writes {3, 5, 5, 4}.
  have hs4_v0 : s4.vregs 0 = q :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 0 (by decide)).trans h_v0
  have hs4_v1 : s4.vregs 1 = rem :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 1 (by decide)).trans h_v1
  have hs4_v2 : s4.vregs 2 = adj :=
    (chain_pres_4 h1_pres h2_pres h3_pres h4_pres 2 (by decide)).trans h_v2
  -- Stitch the bind chain.
  refine ⟨s4, ?_, hs4_v0, hs4_v1, hs4_v2, hs4_sail⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3, bind_run_of_ok h4]
  exact h5

/-- Phase 4 — compute |adj| + `assert_valid_unsigned_remainder v1 v5`.

Guard: `|adj| = 0 ∨ rem.toNat < |adj|.toNat` — either the adjusted
divisor is zero (which makes the assert vacuous, matching the Rust
short-circuit on divisor = 0), or the absolute remainder is strictly
less than the absolute adjusted divisor, unsigned. -/
theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hguard_rem_bound :
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
        rem.toNat <
          ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) :
    ∃ js',
      (phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs 0 = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  -- Step 1: vreg_SRAI 3 2 63 → writes shift_bits_right_arith (s.v2) 63 to v3.
  obtain ⟨s1, h1, h1_v3, h1_pres, h1_sail⟩ := vreg_SRAI_run_ex 3 2 63 js
  -- Step 2: vreg_XOR 5 2 3 → writes (s1.v2 ^^^ s1.v3) to v5.
  obtain ⟨s2, h2, h2_v5, h2_pres, h2_sail⟩ := vreg_XOR_run_ex 5 2 3 s1
  -- Step 3: vreg_SUB 5 5 3 → writes (s2.v5 - s2.v3) to v5.
  obtain ⟨s3, h3, h3_v5, h3_pres, h3_sail⟩ := vreg_SUB_run_ex 5 5 3 s2
  -- Sail propagation.
  have hs3_sail : s3.sail = js.sail := h3_sail.trans (h2_sail.trans h1_sail)
  -- Lookups on s1.
  have hs1_v2 : s1.vregs 2 = adj := (h1_pres 2 (by decide)).trans h_v2
  have hs1_v3 : s1.vregs 3 = adj.sshiftRight 63 := by rw [h1_v3, h_v2]; rfl
  -- Lookups on s2.
  have hs2_v3 : s2.vregs 3 = adj.sshiftRight 63 :=
    (h2_pres 3 (by decide)).trans hs1_v3
  have hs2_v5 : s2.vregs 5 = adj ^^^ adj.sshiftRight 63 := by
    rw [h2_v5, hs1_v2, hs1_v3]
  -- Lookups on s3 — for the assert.
  have hs3_v5 : s3.vregs 5 = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [h3_v5, hs2_v5, hs2_v3]
  have hs3_v1 : s3.vregs 1 = rem :=
    (chain_pres_3 h1_pres h2_pres h3_pres 1 (by decide)).trans h_v1
  -- Step 4: assert v1 < v5 — discharged via hguard_rem_bound.
  have hguard_lt : s3.vregs 5 = 0#64 ∨ (s3.vregs 1).toNat < (s3.vregs 5).toNat := by
    rw [hs3_v1, hs3_v5]; exact hguard_rem_bound
  have h4 : (vreg_assert_valid_unsigned_remainder 1 5).run s3
              = .ok RETIRE_SUCCESS s3 :=
    vreg_assert_valid_unsigned_remainder_run_ok 1 5 s3 hguard_lt
  -- Post-condition: v0 preserved through all 3 writes.
  have hs3_v0 : s3.vregs 0 = q :=
    (chain_pres_3 h1_pres h2_pres h3_pres 0 (by decide)).trans h_v0
  -- Stitch the bind chain.
  refine ⟨s3, ?_, hs3_v0, hs3_sail⟩
  rw [bind_run_of_ok h1, bind_run_of_ok h2, bind_run_of_ok h3]
  exact h4

/-- Phase 5 — writeback `rd := v0`. Writes the quotient to real `rd`
via `liftSail (wX_bits rd q)`; produces `sail = stateAfterWrite js.sail rd q`. -/
theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (phase_writeback rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback
  have hq : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · show vreg_ADDI_to_real rd 0 0 js = _
    exact vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hq]; exact hw)
  · show s' = stateAfterWrite js_ref rd q
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

-- ----------------------------------------------------------------------------
-- Phase-run soundness lemmas (reverse direction)
-- ----------------------------------------------------------------------------
-- Each of these takes `(phase_*.run js = .ok r js₁)` and extracts the
-- guard that the assert inside the phase enforced, plus the same state
-- invariants the forward version establishes. Used by `jolt_div_sound`.

/-- Phase 1 soundness — if `phase_setup` ok-terminates, the div0 guard
must have held and the advice landed in `v0`, `v1` without disturbing
`.sail`. -/
theorem phase_setup_run_sound
    (rs2 : regidx) (q rem : BitVec 64)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : (phase_setup rs2 q rem).run js = .ok r js₁) :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.sail = js.sail := by
  unfold phase_setup at hp
  -- Step 1: unpeel vreg_advice 0 q.
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, hs1_pres, hs1_sail⟩ := vreg_advice_run_ex 0 q js
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: unpeel vreg_advice 1 rem.
  obtain ⟨_, s₂, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₂, hrun2_ex, hs2_v1, hs2_pres, hs2_sail⟩ := vreg_advice_run_ex 1 rem s₁
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: assert. Cross-state lookups for the guard.
  have hs2_v0 : s₂.vregs 0 = q := (hs2_pres 0 (by decide)).trans hs1_v0
  have hs2_sail_orig : s₂.sail = js.sail := hs2_sail.trans hs1_sail
  have hrs2_s2 : rX_bits rs2 s₂.sail = .ok divisor s₂.sail := hs2_sail_orig.symm ▸ hrs2
  -- Case-split on the div0 guard via the assert's _run_ok / _run_err.
  by_cases hguard : (divisor = 0#64 ∧ s₂.vregs 0 ≠ (-1 : BitVec 64))
  · -- guard fires → throw, contradicts .ok
    exfalso
    have herr := vreg_assert_valid_div0_run_err rs2 0 s₂ divisor hrs2_s2 hguard
    change vreg_assert_valid_div0 rs2 0 s₂ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp
  · -- guard holds → state preserved, js₁ = s₂
    have hok := vreg_assert_valid_div0_run_ok rs2 0 s₂ divisor hrs2_s2 hguard
    change vreg_assert_valid_div0 rs2 0 s₂ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    refine ⟨?_, hs2_v0, hs2_v1, hs2_sail_orig⟩
    rw [hs2_v0] at hguard
    exact hguard

/-- Phase 2 soundness — if `phase_overflow_check` ok-terminates given
the standing invariants on `js`, the overflow-check assert's guard
held, and `v2`/`v4` now hold `adj`/`q·adj`. -/
theorem phase_overflow_check_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (hadj : adj = change_divisor_value dividend divisor)
    (hp : (phase_overflow_check rs1 rs2).run js = .ok r js₁) :
    mulhs q adj = (q * adj).sshiftRight 63 ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.vregs 4 = q * adj ∧
    js₁.sail = js.sail := by
  unfold phase_overflow_check at hp
  -- Step 1: vreg_change_divisor 2 rs1 rs2.
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v2, hs1_pres, hs1_sail⟩ :=
    vreg_change_divisor_run_ex 2 rs1 rs2 js dividend divisor hrs1 hrs2
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: vreg_MULH 3 0 2.
  obtain ⟨_, s₂, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₂, hrun2_ex, hs2_v3, hs2_pres, hs2_sail⟩ := vreg_MULH_run_ex 3 0 2 s₁
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: vreg_MUL 4 0 2.
  obtain ⟨_, s₃, hrun3, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₃, hrun3_ex, hs3_v4, hs3_pres, hs3_sail⟩ := vreg_MUL_run_ex 4 0 2 s₂
  rw [hrun3_ex] at hrun3
  cases hrun3
  -- Step 4: vreg_SRAI 5 4 63.
  obtain ⟨_, s₄, hrun4, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₄, hrun4_ex, hs4_v5, hs4_pres, hs4_sail⟩ := vreg_SRAI_run_ex 5 4 63 s₃
  rw [hrun4_ex] at hrun4
  cases hrun4
  -- Cross-state lookups (chained through preservation).
  have hs1_v0 : s₁.vregs 0 = q := (hs1_pres 0 (by decide)).trans h_v0
  have hs1_v2_adj : s₁.vregs 2 = adj := hs1_v2.trans hadj.symm
  have hs2_v0 : s₂.vregs 0 = q := (hs2_pres 0 (by decide)).trans hs1_v0
  have hs2_v2 : s₂.vregs 2 = adj := (hs2_pres 2 (by decide)).trans hs1_v2_adj
  have hs2_v3' : s₂.vregs 3 = mulhs q adj := by rw [hs2_v3, hs1_v0, hs1_v2_adj]
  have hs3_v3 : s₃.vregs 3 = mulhs q adj := (hs3_pres 3 (by decide)).trans hs2_v3'
  have hs3_v4' : s₃.vregs 4 = q * adj := by rw [hs3_v4, hs2_v0, hs2_v2]
  have hs4_v3 : s₄.vregs 3 = mulhs q adj := (hs4_pres 3 (by decide)).trans hs3_v3
  have hs4_v5' : s₄.vregs 5 = (q * adj).sshiftRight 63 := by
    rw [hs4_v5, hs3_v4']; rfl
  -- Step 5: assert v3 = v5. Case-split on the equality guard.
  by_cases hguard_eq : s₄.vregs 3 = s₄.vregs 5
  · -- Derive all post-state facts BEFORE the assert's `cases hp`, since that
    -- substitutes `s₄ → js₁` and dismisses references to `s₄`.
    have hguard : mulhs q adj = (q * adj).sshiftRight 63 := by
      rw [← hs4_v3, hguard_eq, hs4_v5']
    have hs4_v0 : s₄.vregs 0 = q :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 0 (by decide)).trans h_v0
    have hs4_v1 : s₄.vregs 1 = rem :=
      (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 1 (by decide)).trans h_v1
    have hs4_v2 : s₄.vregs 2 = adj :=
      (((hs4_pres 2 (by decide)).trans (hs3_pres 2 (by decide))).trans
        (hs2_pres 2 (by decide))).trans hs1_v2_adj
    have hs4_v4 : s₄.vregs 4 = q * adj := (hs4_pres 4 (by decide)).trans hs3_v4'
    have hs4_sail_orig : s₄.sail = js.sail :=
      hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
    have hok := vreg_assert_eq_run_ok 3 5 s₄ hguard_eq
    change vreg_assert_eq 3 5 s₄ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    exact ⟨hguard, hs4_v0, hs4_v1, hs4_v2, hs4_v4, hs4_sail_orig⟩
  · -- guard fails → throw, contradicts .ok
    exfalso
    have herr := vreg_assert_eq_run_err 3 5 s₄ hguard_eq
    change vreg_assert_eq 3 5 s₄ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

/-- Phase 3 soundness — if `phase_quotient_product` ok-terminates, the
division equation `q·adj + signed_rem = dividend` held. -/
theorem phase_quotient_product_run_sound
    (rs1 : regidx)
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj dividend : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (h_v4 : js.vregs 4 = q * adj)
    (hp : (phase_quotient_product rs1).run js = .ok r js₁) :
    q * adj +
      ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63)
      = dividend ∧
    js₁.vregs 0 = q ∧
    js₁.vregs 1 = rem ∧
    js₁.vregs 2 = adj ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  -- Step 1: vreg_SRAI_from_real 3 rs1 63.
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ :=
    vreg_SRAI_from_real_run_ex 3 rs1 63 js dividend hrs1
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: vreg_XOR 5 1 3.
  obtain ⟨_, s₂, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₂, hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 1 3 s₁
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: vreg_SUB 5 5 3.
  obtain ⟨_, s₃, hrun3, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₃, hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 3 s₂
  rw [hrun3_ex] at hrun3
  cases hrun3
  -- Step 4: vreg_ADD 4 4 5.
  obtain ⟨_, s₄, hrun4, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₄, hrun4_ex, hs4_v4, hs4_pres, hs4_sail⟩ := vreg_ADD_run_ex 4 4 5 s₃
  rw [hrun4_ex] at hrun4
  cases hrun4
  -- Cross-state lookups for the v4 derivation.
  have hs1_v1 : s₁.vregs 1 = rem := (hs1_pres 1 (by decide)).trans h_v1
  have hs1_v3' : s₁.vregs 3 = dividend.sshiftRight 63 := by rw [hs1_v3]; rfl
  have hs1_v4 : s₁.vregs 4 = q * adj := (hs1_pres 4 (by decide)).trans h_v4
  have hs2_v3 : s₂.vregs 3 = dividend.sshiftRight 63 :=
    (hs2_pres 3 (by decide)).trans hs1_v3'
  have hs2_v4 : s₂.vregs 4 = q * adj := (hs2_pres 4 (by decide)).trans hs1_v4
  have hs2_v5' : s₂.vregs 5 = rem ^^^ dividend.sshiftRight 63 := by
    rw [hs2_v5, hs1_v1, hs1_v3']
  have hs3_v4 : s₃.vregs 4 = q * adj := (hs3_pres 4 (by decide)).trans hs2_v4
  have hs3_v5' :
      s₃.vregs 5 = (rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63 := by
    rw [hs3_v5, hs2_v5', hs2_v3]
  have hs4_v4' :
      s₄.vregs 4 =
        q * adj + ((rem ^^^ dividend.sshiftRight 63) - dividend.sshiftRight 63) := by
    rw [hs4_v4, hs3_v4, hs3_v5']
  -- Sail propagation, transport hrs1 to s₄.
  have hs4_sail_orig : s₄.sail = js.sail :=
    hs4_sail.trans (hs3_sail.trans (hs2_sail.trans hs1_sail))
  have hrs1_s4 : rX_bits rs1 s₄.sail = .ok dividend s₄.sail :=
    hs4_sail_orig.symm ▸ hrs1
  -- Step 5: assert v4 = rs1. Case-split on guard.
  by_cases hguard : s₄.vregs 4 = dividend
  · have hok := vreg_assert_eq_real_run_ok 4 rs1 s₄ dividend hrs1_s4 hguard
    change vreg_assert_eq_real 4 rs1 s₄ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    refine ⟨?_, ?_, ?_, ?_, hs4_sail_orig⟩
    · rw [← hs4_v4']; exact hguard
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 0 (by decide)).trans h_v0
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 1 (by decide)).trans h_v1
    · exact (chain_pres_4 hs1_pres hs2_pres hs3_pres hs4_pres 2 (by decide)).trans h_v2
  · exfalso
    have herr := vreg_assert_eq_real_run_err 4 rs1 s₄ dividend hrs1_s4 hguard
    change vreg_assert_eq_real 4 rs1 s₄ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

/-- Phase 4 soundness — if `phase_remainder_bound` ok-terminates, the
unsigned remainder bound holds *or* the adjusted divisor is zero (the
Rust assert short-circuits in that case). -/
theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState) (r : ExecutionResult)
    (q rem adj : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_v1 : js.vregs 1 = rem)
    (h_v2 : js.vregs 2 = adj)
    (hp : (phase_remainder_bound).run js = .ok r js₁) :
    (((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63) = 0#64 ∨
      rem.toNat <
        ((adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63).toNat) ∧
    js₁.vregs 0 = q ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  -- Step 1: vreg_SRAI 3 2 63.
  obtain ⟨_, s₁, hrun1, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₁, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := vreg_SRAI_run_ex 3 2 63 js
  rw [hrun1_ex] at hrun1
  cases hrun1
  -- Step 2: vreg_XOR 5 2 3.
  obtain ⟨_, s₂, hrun2, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₂, hrun2_ex, hs2_v5, hs2_pres, hs2_sail⟩ := vreg_XOR_run_ex 5 2 3 s₁
  rw [hrun2_ex] at hrun2
  cases hrun2
  -- Step 3: vreg_SUB 5 5 3.
  obtain ⟨_, s₃, hrun3, hp⟩ := bind_unpeel_of_ok hp
  obtain ⟨s₃, hrun3_ex, hs3_v5, hs3_pres, hs3_sail⟩ := vreg_SUB_run_ex 5 5 3 s₂
  rw [hrun3_ex] at hrun3
  cases hrun3
  -- Cross-state lookups for the v5 derivation = |adj|.
  have hs1_v2 : s₁.vregs 2 = adj := (hs1_pres 2 (by decide)).trans h_v2
  have hs1_v3' : s₁.vregs 3 = adj.sshiftRight 63 := by rw [hs1_v3, h_v2]; rfl
  have hs2_v3 : s₂.vregs 3 = adj.sshiftRight 63 :=
    (hs2_pres 3 (by decide)).trans hs1_v3'
  have hs2_v5' : s₂.vregs 5 = adj ^^^ adj.sshiftRight 63 := by
    rw [hs2_v5, hs1_v2, hs1_v3']
  have hs3_v5' :
      s₃.vregs 5 = (adj ^^^ adj.sshiftRight 63) - adj.sshiftRight 63 := by
    rw [hs3_v5, hs2_v5', hs2_v3]
  have hs3_v1 : s₃.vregs 1 = rem :=
    (chain_pres_3 hs1_pres hs2_pres hs3_pres 1 (by decide)).trans h_v1
  have hs3_sail_orig : s₃.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  -- Step 4: assert (v5 = 0 ∨ v1 < v5). Case-split on guard.
  by_cases hguard : s₃.vregs 5 = 0#64 ∨ (s₃.vregs 1).toNat < (s₃.vregs 5).toNat
  · have hok := vreg_assert_valid_unsigned_remainder_run_ok 1 5 s₃ hguard
    change vreg_assert_valid_unsigned_remainder 1 5 s₃ = .ok r js₁ at hp
    rw [hok] at hp
    cases hp
    refine ⟨?_, ?_, hs3_sail_orig⟩
    · rcases hguard with h0 | hlt
      · left; rw [← hs3_v5']; exact h0
      · right; rw [← hs3_v1, ← hs3_v5']; exact hlt
    · exact (chain_pres_3 hs1_pres hs2_pres hs3_pres 0 (by decide)).trans h_v0
  · exfalso
    have herr := vreg_assert_valid_unsigned_remainder_run_err 1 5 s₃ hguard
    change vreg_assert_valid_unsigned_remainder 1 5 s₃ = .ok r js₁ at hp
    rw [herr] at hp
    cases hp

/-- Phase 5 soundness — writeback is unconditional; just characterises
the final state. -/
theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState) (r : ExecutionResult)
    (q : BitVec 64)
    (h_v0 : js.vregs 0 = q)
    (h_sail : js.sail = js_ref)
    (hp : (phase_writeback rd).run js = .ok r js₁) :
    js₁.sail = stateAfterWrite js_ref rd q := by
  unfold phase_writeback at hp
  change vreg_ADDI_to_real rd 0 0 js = .ok r js₁ at hp
  have hq : js.vregs (0 : BitVec 7) + sign_extend (m := 64) (0 : BitVec 12) = q := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd q js.sail
  have hp_concrete : vreg_ADDI_to_real rd 0 0 js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } :=
    vreg_ADDI_to_real_run rd 0 0 js s' (by rw [hq]; exact hw)
  rw [hp_concrete] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd q
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd q js.sail s' hw

end
