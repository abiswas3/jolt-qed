import JoltBytecode.SailJoltState.Defs

/-!
# Register Write Lemmas

Properties of wX_bits (RISC-V register writes) proved by exhaustive
case-splitting over all 32 register indices. These are the building
blocks for instruction correctness proofs:

- wX_shape: writing to a register always succeeds
- wX_wX_collapse: two writes to the same register = just the second write
- wX_regs_spec: wX_bits output regs = wX_update_regs (a simple insert)

Also contains the reg_cases tactic and helper lemmas
(eStateM_deterministic, extDHashMap_insert_insert).
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- reg_cases tactic
-- ============================================================================

-- Exhaustively case-split a regidx (BitVec 5) into all 32 values.
-- A regidx wraps a BitVec 5, so there are exactly 32 possible values.
-- After reg_cases r, you get 32 goals, each with h : i.toNat = N.
-- Usage: `reg_cases r <;> simp_all [...]` to close all 32 goals at once.
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

-- ============================================================================
-- Basic read/write properties
-- ============================================================================

-- readReg does not change state. It does get >>= (hash map lookup) >>= pure.
-- None of get, lookup, or pure modify the state.
theorem readReg_pure (reg : Register) (s : SailState) (v : RegisterType reg) (s' : SailState)
    (h : (Sail.readReg reg : SailM (RegisterType reg)) s = .ok v s') : s' = s := by
  unfold Sail.readReg PreSail.readReg at h
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure] at h
  generalize hget : s.regs.get? reg = lookup at h
  cases lookup with
  | some val => cases h; rfl
  | none => exfalso; revert h; simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

-- rX_bits does not change state: if the read succeeds, the output state
-- equals the input state. Each non-zero register branch calls readReg
-- (which doesn't change state by readReg_pure). Register 0 returns
-- pure zero_reg (also doesn't change state).
theorem rX_bits_pure (r : regidx)
    (s : SailState) (v : BitVec 64) (s' : SailState)
    (h : rX_bits r s = .ok v s') : s' = s := by
  unfold rX_bits rX regval_from_reg at h
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, EStateM.bind, pure, EStateM.pure] at h
  -- Case-split on the register index. Use the manual 32-way split.
  obtain ⟨i⟩ := r
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  rcases hcases with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' |
                      h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  -- r=0: pure zero_reg, h says .ok zero_reg s = .ok v s'. Trivially s' = s.
  · simp only [h'] at h; cases h; rfl
  -- r=1..31: each has readReg. Generalize and apply readReg_pure.
  all_goals (
    simp only [h'] at h
    generalize hread : Sail.readReg _ s = result at h
    cases result with
    | error e s'' => exact absurd h (by simp)
    | ok a s'' =>
      simp only [EStateM.Result.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact readReg_pure _ s a s'' hread)

-- wX_bits always succeeds: for any register and value, the write produces
-- some successor state. This is because writeReg on a hash map always works.
theorem wX_shape (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' := by
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

-- EStateM is deterministic: running the same computation on the same state
-- always gives the same result. If we know two runs both succeed, the
-- values and successor states are equal.
theorem eStateM_deterministic {σ ε α : Type} {m : EStateM ε σ α} {s : σ}
    {a1 a2 : α} {s1 s2 : σ}
    (h1 : m s = .ok a1 s1) (h2 : m s = .ok a2 s2) :
    a1 = a2 ∧ s1 = s2 := by
  rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩

-- wX_bits only changes the regs field of the state. All other fields
-- (choiceState, mem, tags, cycleCount, sailOutput) are preserved.
-- Proved as an existential so simp doesn't choke on hypotheses.
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

-- Given that wX_bits r v s succeeded with result s', s' differs from s
-- only in the regs field. Follows from wX_shape_modify + determinism.
theorem wX_eq_modify_regs (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits r v s = .ok () s') :
    s' = { s with regs := s'.regs } := by
  have ⟨s'', hs'', hmod⟩ := wX_shape_modify r v s
  have ⟨_, heq⟩ := eStateM_deterministic hw hs''
  subst heq; exact hmod

-- ============================================================================
-- wX_bits regs specification via wX_update_regs
-- ============================================================================

-- wX_update_regs is a simple pure function that mirrors what wX_bits does
-- to the regs field. For register 0 it's a no-op (x0 is hardwired to zero).
-- For register N it inserts the value into the hash map at key xN.
--
-- Sail's wX_bits goes through a long chain
-- (wX_bits → wX → writeReg → modify → regs.insert), but the net effect
-- on the regs field is just wX_update_regs — a simple match-then-insert.
-- This lets us reason about the regs output without unfolding all the
-- Sail monadic machinery.
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

-- wX_bits r v s produces a state whose regs = wX_update_regs r v s.regs.
-- This links the Sail monadic write to the pure function above.
theorem wX_regs_spec (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' ∧ s'.regs = wX_update_regs r v s.regs := by
  unfold wX_bits wX regval_into_reg wX_update_regs
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits, modify, modifyGet] <;>
    exact ⟨_, rfl, rfl⟩

-- ============================================================================
-- Hash map and double-write lemmas
-- ============================================================================

-- Inserting the same key twice into an ExtDHashMap: only the last value
-- matters. This is the hash map analogue of "the last write wins."
theorem extDHashMap_insert_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    {β : α → Type} (m : Std.ExtDHashMap α β) (k : α) (v1 v2 : β k) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  simp [Std.ExtDHashMap.get?_insert]
  split <;> simp_all

-- wX_update_regs is idempotent: applying it twice with the same register
-- but different values gives the same result as applying it once with the
-- second value. Follows from extDHashMap_insert_insert for non-zero registers,
-- and is trivially true for register 0 (which is a no-op).
theorem wX_update_regs_idem (r : regidx) (v1 v2 : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType) :
    wX_update_regs r v2 (wX_update_regs r v1 regs) = wX_update_regs r v2 regs := by
  unfold wX_update_regs
  obtain ⟨i⟩ := r
  reg_cases (regidx.Regidx i) <;> simp_all [extDHashMap_insert_insert]

-- ============================================================================
-- wX_wX_collapse: writing the same register twice = just the second write
-- ============================================================================

-- If you write v1 to register r (getting state s1), then write v2 to the
-- same register r (getting state s2), the net effect is the same as writing
-- v2 directly from the original state s. The first write is overwritten.
--
-- Proof strategy: get a witness s3 from wX_shape (single write of v2),
-- show s3 = s2 by comparing regs (via wX_regs_spec + wX_update_regs_idem)
-- and non-regs fields (via wX_eq_modify_regs).
theorem wX_wX_collapse (r : regidx) (v1 v2 : BitVec 64) (s s1 s2 : SailState)
    (hw1 : wX_bits r v1 s = .ok () s1) (hw2 : wX_bits r v2 s1 = .ok () s2) :
    wX_bits r v2 s = .ok () s2 := by
  obtain ⟨s3, hs3⟩ := wX_shape r v2 s
  suffices s3 = s2 by rw [this] at hs3; exact hs3
  have ⟨_, h1ok, h1regs⟩ := wX_regs_spec r v1 s
  have ⟨_, h2ok, h2regs⟩ := wX_regs_spec r v2 s1
  have ⟨_, h3ok, h3regs⟩ := wX_regs_spec r v2 s
  have ⟨_, e1⟩ := eStateM_deterministic hw1 h1ok; subst e1
  have ⟨_, e2⟩ := eStateM_deterministic hw2 h2ok; subst e2
  have ⟨_, e3⟩ := eStateM_deterministic hs3 h3ok; subst e3
  have h_regs : s2.regs = s3.regs := by
    rw [h2regs, h1regs, wX_update_regs_idem, ← h3regs]
  have hm1 := wX_eq_modify_regs r v1 s s1 hw1
  have hm2 := wX_eq_modify_regs r v2 s1 s2 hw2
  have hm3 := wX_eq_modify_regs r v2 s s3 hs3
  rw [hm3, hm2, hm1]; simp [h_regs]

end
