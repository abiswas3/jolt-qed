import LeanRV64D

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

/-!
# Common infrastructure for Jolt ↔ SailM equivalence proofs

Contains: SailJoltState, JoltMonad, projection, liftSail, register lemmas,
BitVec lemmas, jolt_virtual_sign_extend_word.

Individual instruction proofs (Addw.lean, Subw.lean, etc.) import this.
-/

-- ============================================================================
-- Types
-- ============================================================================
abbrev SailState := SequentialState RegisterType trivialChoiceSource

structure SailJoltState where
  regs        : Std.ExtDHashMap Register RegisterType
  choiceState : Unit
  mem         : Std.ExtHashMap Nat (BitVec 8)
  tags        : Unit
  cycleCount  : Nat
  sailOutput  : Array String
  -- These are extra Jolt specific things
  -- NOTE: We do not use the first 32 registers, instead we use regs as those regs 
  -- are already in RISCV-CPU
  vregs       : BitVec 7 → BitVec 64 := fun _ => 0

abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- ============================================================================
-- Projection
-- ============================================================================

def project (js : SailJoltState) : SailState where
  regs := js.regs;
  choiceState := js.choiceState;
  mem := js.mem
  tags := js.tags;
  cycleCount := js.cycleCount;
  sailOutput := js.sailOutput

-- Replace all fields of SailJoltState that are common with SailState
-- with the SailState values
def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with regs := ss.regs, choiceState := ss.choiceState,
            mem := ss.mem, tags := ss.tags,
            cycleCount := ss.cycleCount, sailOutput := ss.sailOutput }

-- Take the result of a Jolt step and project it down to a Sail result
-- by stripping the Jolt-only fields.
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- ============================================================================
-- liftSail
-- ============================================================================
def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m (project js) with
  | .ok a ss' => .ok a (inject js ss')
  | .error e ss' => .error e (inject js ss')

theorem liftSail_project (m : SailM α) (js : SailJoltState) :
    projectResult ((liftSail m).run js) = m.run (project js) := by
  simp only [liftSail, projectResult, project, inject, EStateM.run]
  cases m ⟨js.regs, js.choiceState, js.mem, js.tags, js.cycleCount, js.sailOutput⟩ <;> simp_all

-- ============================================================================
-- Virtual register operations
-- ============================================================================
-- Read the contents of a virtual register.
def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

-- Write to a virtual regigster.
def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

-- ============================================================================
-- Sail register lemmas
-- wX_shape: proved. wX_rX_roundtrip, wX_wX_collapse: sorry (to be proved).
-- ============================================================================

-- Exhaustively case-split a regidx (BitVec 5) into all 32 values.
-- Usage: `reg_cases r` where `r : regidx`, then apply a finishing tactic
-- to all 32 goals with `<;> ...`.
syntax "reg_cases" term : tactic
macro_rules
  | `(tactic| reg_cases $r:term) => `(tactic| (
      obtain ⟨i⟩ := $r
      have hi : i.toNat < 32 := i.isLt
      have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
        i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
        i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
        i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
        i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
        i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
        i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
        i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
      rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                         h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h))

-- wX_bits always succeeds.
theorem wX_shape (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' := by
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

-- EStateM is deterministic: same computation on same state gives same result.
theorem eStateM_deterministic {σ ε α : Type} {m : EStateM ε σ α} {s : σ}
    {a1 a2 : α} {s1 s2 : σ}
    (h1 : m s = .ok a1 s1) (h2 : m s = .ok a2 s2) :
    a1 = a2 ∧ s1 = s2 := by
  rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩

-- wX_bits only changes regs; all other state fields are preserved.
-- Proved as an existential (no hypotheses) so simp_all doesn't choke.
theorem wX_shape_modify (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' ∧ s' = { s with regs := s'.regs } := by
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits, modify, modifyGet] <;>
    first
    | exact ⟨_, rfl, rfl⟩
    | (refine ⟨_, rfl, ?_⟩; cases s; rfl)

theorem wX_eq_modify_regs (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits r v s = .ok () s') :
    s' = { s with regs := s'.regs } := by
  have ⟨s'', hs'', hmod⟩ := wX_shape_modify r v s
  have ⟨_, heq⟩ := eStateM_deterministic hw hs''
  subst heq; exact hmod

-- ============================================================================
-- wX_bits regs specification
-- ============================================================================

-- Explicit characterization of what wX_bits does to regs, per register index.
noncomputable def wX_update_regs (r : regidx) (v : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType) :
    Std.ExtDHashMap Register RegisterType :=
  match r with
  | ⟨i⟩ =>
    let w := regval_into_reg v
    match i.toNat with
    | 0 => regs
    | 1 => regs.insert Register.x1 w  | 2 => regs.insert Register.x2 w
    | 3 => regs.insert Register.x3 w  | 4 => regs.insert Register.x4 w
    | 5 => regs.insert Register.x5 w  | 6 => regs.insert Register.x6 w
    | 7 => regs.insert Register.x7 w  | 8 => regs.insert Register.x8 w
    | 9 => regs.insert Register.x9 w  | 10 => regs.insert Register.x10 w
    | 11 => regs.insert Register.x11 w | 12 => regs.insert Register.x12 w
    | 13 => regs.insert Register.x13 w | 14 => regs.insert Register.x14 w
    | 15 => regs.insert Register.x15 w | 16 => regs.insert Register.x16 w
    | 17 => regs.insert Register.x17 w | 18 => regs.insert Register.x18 w
    | 19 => regs.insert Register.x19 w | 20 => regs.insert Register.x20 w
    | 21 => regs.insert Register.x21 w | 22 => regs.insert Register.x22 w
    | 23 => regs.insert Register.x23 w | 24 => regs.insert Register.x24 w
    | 25 => regs.insert Register.x25 w | 26 => regs.insert Register.x26 w
    | 27 => regs.insert Register.x27 w | 28 => regs.insert Register.x28 w
    | 29 => regs.insert Register.x29 w | 30 => regs.insert Register.x30 w
    | _ => regs.insert Register.x31 w

-- Factoring lemma: Sail's wX_bits goes through a long chain
-- (wX_bits → wX → writeReg → modify → regs.insert), but the net effect
-- on the regs field is just wX_update_regs — a simple match-then-insert.
-- This lets us reason about the regs output without unfolding all the
-- Sail monadic machinery, similar to how we factor Sail instructions
-- into simpler equivalent forms for the main correctness proofs.
theorem wX_regs_spec (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' ∧ s'.regs = wX_update_regs r v s.regs := by
  unfold wX_bits wX regval_into_reg wX_update_regs
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits, modify, modifyGet] <;>
    exact ⟨_, rfl, rfl⟩

-- insert-insert on ExtDHashMap: inserting the same key twice collapses.
theorem extDHashMap_insert_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    {β : α → Type} (m : Std.ExtDHashMap α β) (k : α) (v1 v2 : β k) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  simp [Std.ExtDHashMap.get?_insert]
  split <;> simp_all

-- Two writes to the same register: the update function is idempotent.
theorem wX_update_regs_idem (r : regidx) (v1 v2 : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType) :
    wX_update_regs r v2 (wX_update_regs r v1 regs) = wX_update_regs r v2 regs := by
  unfold wX_update_regs
  obtain ⟨i⟩ := r
  reg_cases (regidx.Regidx i) <;> simp_all [extDHashMap_insert_insert]

-- ============================================================================
-- wX_wX_collapse: writing the same register twice = just the second write
-- ============================================================================

theorem wX_wX_collapse (r : regidx) (v1 v2 : BitVec 64) (s s1 s2 : SailState)
    (hw1 : wX_bits r v1 s = .ok () s1) (hw2 : wX_bits r v2 s1 = .ok () s2) :
    wX_bits r v2 s = .ok () s2 := by
  -- Get s3 from single write of v2 to s
  obtain ⟨s3, hs3⟩ := wX_shape r v2 s
  suffices s3 = s2 by rw [this] at hs3; exact hs3
  -- Get regs specs and link to actual states via determinism
  have ⟨_, h1ok, h1regs⟩ := wX_regs_spec r v1 s
  have ⟨_, h2ok, h2regs⟩ := wX_regs_spec r v2 s1
  have ⟨_, h3ok, h3regs⟩ := wX_regs_spec r v2 s
  have ⟨_, e1⟩ := eStateM_deterministic hw1 h1ok; subst e1
  have ⟨_, e2⟩ := eStateM_deterministic hw2 h2ok; subst e2
  have ⟨_, e3⟩ := eStateM_deterministic hs3 h3ok; subst e3
  -- s2.regs = wX_update r v2 (wX_update r v1 s.regs) = wX_update r v2 s.regs = s3.regs
  have h_regs : s2.regs = s3.regs := by
    rw [h2regs, h1regs, wX_update_regs_idem, ← h3regs]
  -- Both states are { s with regs := ... }, so equal when regs match
  have hm1 := wX_eq_modify_regs r v1 s s1 hw1
  have hm2 := wX_eq_modify_regs r v2 s1 s2 hw2
  have hm3 := wX_eq_modify_regs r v2 s s3 hs3
  rw [hm3, hm2, hm1]; simp [h_regs]

-- wX_rX_roundtrip is in RegisterLemmas.lean (separate file to avoid simp interactions).


-- ============================================================================
-- Tactic: sail_cases
--
-- Problem: In the monadic simulation proofs (e.g., jolt_addw_eq_sail),
-- after unfolding definitions with `simp only [...]`, the goal has the form:
--
--   (match rX_bits rs1 s with | .ok v s' => ... | .error e s' => ...) =
--   (match rX_bits rs1 s with | .ok v s' => ... | .error e s' => ...)
--
-- Both sides share the same match discriminant (e.g., `rX_bits rs1 s`).
-- We need to case-split on that shared term so both sides reduce together.
--
-- Why not `split`? The `split` tactic targets the outermost match in the
-- goal, which is typically a `liftSail`/`projectResult` wrapper — not the
-- inner `rX_bits` call we care about. It also doesn't substitute on both
-- sides simultaneously.
--
-- How it works:
--   1. `generalize t = _sc` — replaces ALL occurrences of `t` in the goal
--      with a fresh variable `_sc`. This is key: it captures the term on
--      BOTH sides of the equation.
--   2. `cases _sc` — case-splits `_sc : EStateM.Result` into `.ok` / `.error`.
--   3. `<;> simp` — applied to ALL resulting goals:
--      - Error branches: `simp` closes them (both sides reduce to .error).
--      - Ok branches: `simp` normalizes, leaving the next monadic step.
--
-- Usage (in proof):
--   sail_cases rX_bits rs1 ⟨js.regs, js.choiceState, ...⟩
--   rename_i v1 s1          -- name the auto-generated ok-branch variables
--   sail_cases rX_bits rs2 s1
--   rename_i v2 s2
--   -- now at the domain-specific part of the proof
-- ============================================================================

syntax "sail_cases" term : tactic
macro_rules
  | `(tactic| sail_cases $t:term) => `(tactic|
      (generalize $t = _sc; cases _sc <;> simp))

-- ============================================================================
-- Shared Jolt instructions
-- TODO: Add the remaining ones we need as needed.
-- ============================================================================

-- Virtual sign-extend-word: read rd, sign-extend lower 32 bits, write back.
def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

-- ============================================================================
-- BitVec lemmas
-- ============================================================================

-- Adding and then truncating is the same as truncating and then adding
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

-- Similar to above but for subtraction.
-- Truncating to 32 bits distributes over subtraction.
theorem extractLsb_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a - b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

end
