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

def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

-- ============================================================================
-- Sail register lemmas
-- wX_shape: proved. wX_rX_roundtrip, wX_wX_collapse: sorry (to be proved).
-- ============================================================================

-- wX_bits always succeeds.
theorem wX_shape (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' := by
  obtain ⟨i⟩ := r
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
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
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

-- After writing v to rd, reading rd gives v back.
theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by sorry

-- In plain English: If you write v1 to register r (taking state s to s1),
-- then write v2 to the same register r (taking state s1 to s2), the net
-- effect is the same as writing v2 directly from the original state s.
-- The first write is "overwritten" — only the final value matters.
theorem wX_wX_collapse (r : regidx) (v1 v2 : BitVec 64) (s s1 s2 : SailState)
    (hw1 : wX_bits r v1 s = .ok () s1) (hw2 : wX_bits r v2 s1 = .ok () s2) :
    wX_bits r v2 s = .ok () s2 := by sorry

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
