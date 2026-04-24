import JoltBytecode.EmbeddedSailJoltState.RtypeW
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamily.Primitives

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Toy program for prototyping bind-chain proof strategies

A three-instruction prefix of `jolt_div` — the first two advice loads
and the first assertion — lives here so we can experiment with proof
tactics (in particular, ways to walk a long chain of `EStateM.bind`s)
on a small enough sequence to reason about by hand. `Div.lean` stays
untouched; any primitives we need come via import.
-/

/-- A three-instruction prefix of `jolt_div` — the first two advice loads
and the first assertion. Succeeds iff either `rs2 ≠ 0` in `js.sail` or
`quotient = -1`; otherwise the `VirtualAssertValidDiv0` step throws.
Small enough to experiment with a `bind_chain`-style tactic without the
18-step cognitive load. -/
def toy_program (rs2 : regidx) (quotient rem_abs : BitVec 64) :
    JoltMonad ExecutionResult := do
  let _ ← vreg_advice 0 quotient                      -- VirtualAdvice v0, 0
  let _ ← vreg_advice 1 rem_abs                       -- VirtualAdvice v1, 0
  vreg_assert_valid_div0 rs2 0                        -- VirtualAssertValidDiv0 rs2, v0, 0

-- ----------------------------------------------------------------------------
-- `vreg_advice` desugaring reference
-- ----------------------------------------------------------------------------
-- The original definition in VirtualInstructions.lean uses `do`:
--   def vreg_advice vd advice : JoltMonad ExecutionResult := do
--     writeVReg vd advice
--     pure RETIRE_SUCCESS
--
-- These are the same function at decreasing levels of sugar. The `rfl`
-- proofs below say explicitly which levels are definitionally equal to
-- the original; any that aren't need the simp set.

/-- Level 1: `do` desugars to a bind chain. -/
def vreg_advice_v1 (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult :=
  writeVReg vd advice >>= fun _ => pure RETIRE_SUCCESS

example (vd : BitVec 7) (a : BitVec 64) : vreg_advice vd a = vreg_advice_v1 vd a := by rfl

/-- Level 2: `>>=` resolves through the `Monad` instance to `EStateM.bind`. -/
def vreg_advice_v2 (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult :=
  EStateM.bind (writeVReg vd advice) (fun _ => pure RETIRE_SUCCESS)

example (vd : BitVec 7) (a : BitVec 64) : vreg_advice vd a = vreg_advice_v2 vd a := by rfl

/-- Level 3: `EStateM.bind` inlined — a literal state transformer. -/
def vreg_advice_v3 (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult :=
  fun js =>
    match writeVReg vd advice js with
    | .ok _    s' => .ok RETIRE_SUCCESS s'
    | .error e s' => .error e s'

example (vd : BitVec 7) (a : BitVec 64) : vreg_advice vd a = vreg_advice_v3 vd a := by rfl

/-- Level 4: `writeVReg` has no error path, so the match collapses. This
is the pure state update that `vreg_advice_run` proves. -/
def vreg_advice_v4 (vd : BitVec 7) (advice : BitVec 64) : JoltMonad ExecutionResult :=
  fun js => .ok RETIRE_SUCCESS
    { js with vregs := fun r => if r = vd then advice else js.vregs r }

example (vd : BitVec 7) (a : BitVec 64) : vreg_advice vd a = vreg_advice_v4 vd a := by
  funext js
  unfold vreg_advice  vreg_advice_v4
  -- At this point in the code everying is written pure bind notation. 
  -- As vreg_advice has a do block with 2 lines of code, 
  -- we will see one bind operation.
  -- In general n lines will have n-1 binds.
  simp only [bind, EStateM.bind]
  simp only [pure]
  simp only [EStateM.pure]
  -- What this does is reduce the bind notation to the actual match code
  unfold writeVReg
  --- This is simple definitional rw, i did not to make goal state pretty.
  simp only [modify]
  simp only [modifyGet]
  simp only [MonadStateOf.modifyGet]
  simp only [EStateM.modifyGet]

-- ----------------------------------------------------------------------------
-- Per-step lemmas: what each `vreg_*` primitive does to the state
-- ----------------------------------------------------------------------------
-- The idea is that each Jolt-ISA primitive used in `toy_program` gets a
-- single closed-form characterisation of its `.run` on an arbitrary
-- state. Once all three lemmas are in hand, `toy_program_succeeds`
-- should close by rewriting with them in sequence — no deep nested
-- `match` on `EStateM.Result`.

/-- `vreg_advice vd v` always succeeds and its only effect is to update
the `vd` slot of `js.vregs`. The Sail state is untouched. -/
theorem vreg_advice_run (vd : BitVec 7) (v : BitVec 64) (js : SailJoltState) :
    (vreg_advice vd v).run js =
      .ok RETIRE_SUCCESS
        { js with vregs := fun r => if r = vd then v else js.vregs r } := by
  unfold vreg_advice writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `vreg_assert_valid_div0 rs2 vq` succeeds and leaves the state
unchanged whenever its guard is satisfied (it is *not* the case that
`rs2 = 0` while `vq ≠ -1`). Requires that reading `rs2` from
`js.sail` returns a concrete `divisor` value without side effects. -/
theorem vreg_assert_valid_div0_run_ok (rs2 : regidx) (vq : BitVec 7)
    (js : SailJoltState) (divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : ¬ (divisor = 0#64 ∧ js.vregs vq ≠ (-1 : BitVec 64))) :
    (vreg_assert_valid_div0 rs2 vq).run js = .ok RETIRE_SUCCESS js := by
  -- Step 1 — unfold the two definitions into the raw bind chain.
  --   `vreg_assert_valid_div0` desugars to: liftSail(rX_bits rs2) >>= …
  --   `liftSail` is a plain def; unfolding exposes its `match m js.sail with …`.
  unfold vreg_assert_valid_div0 
  unfold liftSail
  -- Step 2 — drop the `.run` wrapper.
  --   `EStateM.run m s` is by definition just `m s` — it's the applicator
  --   that turns a step function into its result. After this the top of
  --   the goal is a direct application on `js`, and you can *see* the
  --   initial state on the LHS.
  simp only [EStateM.run]
  -- Step 3 — resolve the two `>>=` calls.
  --   `bind` unfolds the typeclass projection Bind.bind → EStateM.bind,
  --   then `EStateM.bind` unfolds the definition body into a nested
  --   `match … with | .ok a s' => … | .error e s' => …`. At this point
  --   the state-threading is explicit: you can see `rX_bits rs2 js.sail`
  --   on the LHS and the new states `s'` in the match patterns.
  simp only [bind, EStateM.bind]
  -- Step 3 — substitute the known read of rs2.
  --   `rX_bits rs2 js.sail` is nested inside a `match`, so plain `rw` can't
  --   reach it; `simp only [hrs2]` rewrites at any depth. After this the
  --   outer match collapses to its `.ok` branch by iota.
  simp only [hrs2]
  -- Step 4 — collapse `readVReg vq …` via its @[simp] lemma
  --   `readVReg_run : readVReg vq s = .ok (s.vregs vq) s`. This fires the
  --   next match on `.ok`, exposing the `if … then throw else pure …`.
  simp only [readVReg_run]
  -- Step 5 — the guard condition is false by assumption `hguard`, so the
  --   if-then-else takes its else branch, leaving `pure RETIRE_SUCCESS`.
  rw [if_neg hguard]
  -- Step 6 — unfold the pure so its body appears as a literal `.ok …`.
  --   After this, the LHS is `.ok RETIRE_SUCCESS { sail := js.sail, vregs := js.vregs }`
  --   and `simp`'s definitional closer collapses the reconstructed record
  --   back to `js` via structure eta, finishing the proof.
  simp only [pure, EStateM.pure]

-- ----------------------------------------------------------------------------
-- Bind-peel helper: the glue that lets per-step lemmas compose
-- ----------------------------------------------------------------------------

/-- If a monadic computation `m` runs to `.ok a js₁` starting from `js`,
then `(m >>= f).run js` equals `(f a).run js₁`. One application of this
lemma "peels off" the first step of a bind chain and reveals the next
step's starting state. -/
theorem bind_run_of_ok {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    {js js₁ : SailJoltState} {a : α}
    (h : m.run js = .ok a js₁) :
    (m >>= f).run js = (f a).run js₁ := by
  show (m >>= f) js = (f a) js₁
  simp only [bind, EStateM.bind]
  -- This is re-writing  m js = .ok a js₁ into h instead of goal. 
  -- why? cos h: m.run js and not m js
  -- rw [show m js = .ok a js₁ from h]
  -- Altenratively this also works 
  have h': m js = .ok a js₁ := by
    exact h
  rw[h']

/-- **Match-peel variant** of `bind_run_of_ok`, for reference.

`match ← m with | pat => body` desugars to `m >>= fun x => match x with | pat => body`,
so this lemma is literally the same statement as `bind_run_of_ok` —
the `branches` function *is* the `fun x => match x with …`. After one
application, the goal has `(branches a)` with `a` concrete, and a
trailing `simp only []` (or `rfl`) collapses the match via iota to the
fired branch.

Kept as a separate named lemma so proofs that walk a match-heavy
chain (e.g. load-family `match ← vreg_LD 1 1 0 with | .Retire_Success () => …`)
read naturally. -/
theorem match_run_of_ok {α β : Type} {m : JoltMonad α}
    {branches : α → JoltMonad β}
    {js js₁ : SailJoltState} {a : α}
    (h : m.run js = .ok a js₁) :
    (m >>= fun x => branches x).run js = (branches a).run js₁ :=
  bind_run_of_ok h


-- ----------------------------------------------------------------------------
-- Sanity check — composed from the per-step lemmas via `bind_run_of_ok`
-- ----------------------------------------------------------------------------

/-- **Sanity check for `toy_program`.** With `rs2` holding any non-zero
value — `10` here — the `VirtualAssertValidDiv0` guard is vacuous, so
the 3-step chain runs to `.ok RETIRE_SUCCESS` regardless of the
advice values. Proved by three `rw` applications of the per-step
lemmas, glued by `bind_run_of_ok`. -/
theorem toy_program_succeeds (rs2 : regidx) (js : SailJoltState)
    (hrs2 : rX_bits rs2 js.sail = .ok (10 : BitVec 64) js.sail) :
    ∃ js', (toy_program rs2 (5 : BitVec 64) (2 : BitVec 64)).run js =
      .ok RETIRE_SUCCESS js' := by

  --------------------------------------------------------------------
  -- PART A — build a "snapshot" of the state after every single step.
  --------------------------------------------------------------------

  -- A.1  Define js₁: the state we expect after Step 1 runs.
  --      Step 1 is `vreg_advice 0 5`, which writes 5 into virtual reg 0
  --      and leaves everything else untouched.
  let js₁ : SailJoltState :=
    { js with
        vregs := fun r => if r = 0 then (5 : BitVec 64) else js.vregs r }

  -- A.2  Prove that running Step 1 from `js` indeed gives `.ok … js₁`.
  --      This is exactly what the per-step lemma `vreg_advice_run` says
  --      for any vd, v, and starting state.
  have hstep1 :
      (vreg_advice 0 (5 : BitVec 64)).run js = .ok RETIRE_SUCCESS js₁ := by
    exact vreg_advice_run 0 5 js

  -- A.3  Define js₂: the state after Step 2 runs, starting from js₁.
  --      Step 2 is `vreg_advice 1 2`; writes 2 into virtual reg 1.
  let js₂ : SailJoltState :=
    { js₁ with
        vregs := fun r => if r = 1 then (2 : BitVec 64) else js₁.vregs r }

  -- A.4  Prove Step 2 goes from js₁ to js₂ cleanly.
  have hstep2 :
      (vreg_advice 1 (2 : BitVec 64)).run js₁ = .ok RETIRE_SUCCESS js₂ := by
    exact vreg_advice_run 1 2 js₁

  --------------------------------------------------------------------
  -- PART B — prepare the preconditions of Step 3.
  --------------------------------------------------------------------

  -- B.1  `vreg_assert_valid_div0_run_ok` wants a hypothesis about
  --      `rX_bits rs2 js₂.sail`, not `rX_bits rs2 js.sail`. But Steps
  --      1 and 2 only modified `vregs`; they never touched `sail`. So
  --      `js₂.sail` is definitionally equal to `js.sail`, and our
  --      original `hrs2` already discharges the obligation.
  have hrs2' :
      rX_bits rs2 js₂.sail = .ok (10 : BitVec 64) js₂.sail := by
    exact hrs2

  -- B.2  Step 3's guard must be false: we must NOT be in the case
  --      "divisor = 0 ∧ quotient ≠ -1". Here divisor is 10 (not 0),
  --      so the conjunction is false no matter what v0 holds. We
  --      show this by assuming the conjunction and deriving absurd
  --      from the left conjunct `(10 : BitVec 64) = 0#64`.
  have hguard :
      ¬ ((10 : BitVec 64) = 0#64 ∧ js₂.vregs 0 ≠ (-1 : BitVec 64)) := by
    intro hconj
    obtain ⟨h0, _⟩ := hconj
    exact absurd h0 (by decide)

  -- B.3  Prove Step 3 runs to `.ok RETIRE_SUCCESS js₂` (state unchanged,
  --      because `vreg_assert_valid_div0` is a pure read+check).
  have hstep3 :
      (vreg_assert_valid_div0 rs2 0).run js₂ = .ok RETIRE_SUCCESS js₂ := by
    exact vreg_assert_valid_div0_run_ok rs2 0 js₂ 10 hrs2' hguard

  --------------------------------------------------------------------
  -- PART C — stitch the three step facts into the full equivalence.
  --------------------------------------------------------------------

  -- C.1  The existential claims "there exists some final state js'".
  --      We pick js₂ as that witness and reduce the goal to proving
  --      the run-equation with js' = js₂ plugged in.
  refine ⟨js₂, ?_⟩

  -- C.2  Now the goal is `(toy_program rs2 5 2).run js = .ok … js₂`.
  --      Unfold `toy_program` to expose the raw bind chain:
  --        vreg_advice 0 5 >>= fun _ =>
  --          vreg_advice 1 2 >>= fun _ =>
  --            vreg_assert_valid_div0 rs2 0
  unfold toy_program

  -- C.3  Peel Step 1 off the chain using `bind_run_of_ok hstep1`.
  --      Before: `(vreg_advice 0 5 >>= rest).run js = .ok … js₂`
  --      After : `(rest ()).run js₁ = .ok … js₂`
  --      i.e.  `(vreg_advice 1 2 >>= tail).run js₁ = .ok … js₂`
  rw [bind_run_of_ok hstep1]

  -- C.4  Peel Step 2 off the (now one-shorter) chain using hstep2.
  --      Before: `(vreg_advice 1 2 >>= tail).run js₁ = .ok … js₂`
  --      After : `(tail ()).run js₂ = .ok … js₂`
  --      i.e.  `(vreg_assert_valid_div0 rs2 0).run js₂ = .ok … js₂`
  rw [bind_run_of_ok hstep2]

  -- C.5  The remaining goal is exactly Step 3's run equation, which
  --      hstep3 discharges.
  exact hstep3

end
