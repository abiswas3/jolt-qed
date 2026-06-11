import JoltBytecode.JoltISA.Operands

/-!
# Register operation lemmas (independent of SailJoltState architecture)

These lemmas are about SailState operations (wX_bits, rX_bits).
They don't reference SailJoltState at all.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- reg_cases tactic
-- ============================================================================

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
-- readReg / rX_bits purity
-- ============================================================================

theorem readReg_pure (reg : Register) (s : SailState) (v : RegisterType reg) (s' : SailState)
    (h : (Sail.readReg reg : SailM (RegisterType reg)) s = .ok v s') : s' = s := by
  unfold Sail.readReg PreSail.readReg at h
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure] at h
  generalize hget : s.regs.get? reg = lookup at h
  cases lookup with
  | some val => cases h; rfl
  | none => exfalso; revert h; simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem rX_bits_pure (r : regidx) (s : SailState) (v : BitVec 64) (s' : SailState)
    (h : rX_bits r s = .ok v s') : s' = s := by
  unfold rX_bits rX regval_from_reg at h
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, EStateM.bind, pure, EStateM.pure] at h
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
  · simp only [h'] at h; cases h; rfl
  all_goals (
    simp only [h'] at h
    generalize hread : Sail.readReg _ s = result at h
    cases result with
    | error e s'' => exact absurd h (by simp)
    | ok a s'' =>
      simp only [EStateM.Result.ok.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact readReg_pure _ s a s'' hread)

/-- Reading architectural register `x0` always returns zero and leaves the Sail
state unchanged. -/
theorem rX_bits_regidx_zero (s : SailState) :
    rX_bits (regidx.Regidx 0) s = .ok 0#64 s := by
  unfold rX_bits rX regval_from_reg zero_reg zeros
  simp [Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

-- ============================================================================
-- wX_bits lemmas
-- ============================================================================

--- TODO: Write always succeeds is the theorem but we have not given it a proper description yet.
theorem wX_shape (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' := by
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

/-- Writing architectural register `x0` always succeeds and leaves the Sail
state unchanged. -/
theorem wX_bits_regidx_zero (v : BitVec 64) (s : SailState) :
    wX_bits (regidx.Regidx 0) v s = .ok () s := by
  unfold wX_bits wX regval_into_reg
  simp [Sail.BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]

theorem eStateM_deterministic {σ ε α : Type} {m : EStateM ε σ α} {s : σ}
    {a1 a2 : α} {s1 s2 : σ}
    (h1 : m s = .ok a1 s1) (h2 : m s = .ok a2 s2) :
    a1 = a2 ∧ s1 = s2 := by
  rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩

theorem wX_shape_modify (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' ∧ s' = { s with regs := s'.regs } := by
  unfold wX_bits wX regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, bind, pure]
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

theorem wX_regs_spec (r : regidx) (v : BitVec 64) (s : SailState) :
    ∃ s', wX_bits r v s = .ok () s' ∧ s'.regs = wX_update_regs r v s.regs := by
  unfold wX_bits wX regval_into_reg wX_update_regs
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits, modify, modifyGet] <;>
    exact ⟨_, rfl, rfl⟩

theorem extDHashMap_insert_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    {β : α → Type} (m : Std.ExtDHashMap α β) (k : α) (v1 v2 : β k) :
    (m.insert k v1).insert k v2 = m.insert k v2 := by
  apply Std.ExtDHashMap.ext_get?
  intro a
  simp [Std.ExtDHashMap.get?_insert]
  split <;> simp_all

theorem wX_update_regs_idem (r : regidx) (v1 v2 : BitVec 64)
    (regs : Std.ExtDHashMap Register RegisterType) :
    wX_update_regs r v2 (wX_update_regs r v1 regs) = wX_update_regs r v2 regs := by
  unfold wX_update_regs
  obtain ⟨i⟩ := r
  reg_cases (regidx.Regidx i) <;> simp_all [extDHashMap_insert_insert]

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

-- ============================================================================
-- wX_rX_roundtrip (via rX_after_wX)
-- ============================================================================

-- readReg after insert on the same key returns the inserted value.
theorem readReg_insert_self (reg : Register) (v : RegisterType reg) (s : SailState) :
    (PreSail.readReg reg : SailM (RegisterType reg))
      { s with regs := s.regs.insert reg v } =
    .ok v { s with regs := s.regs.insert reg v } := by
  unfold PreSail.readReg
  simp only [bind, get, getThe, EStateM.bind, EStateM.get, MonadStateOf.get,
             Std.ExtDHashMap.get?_insert_self, pure, EStateM.pure]

theorem rX_after_wX (r : regidx) (v : BitVec 64) (s : SailState)
    (hr : r ≠ regidx.Regidx 0) :
    rX_bits r { s with regs := wX_update_regs r v s.regs } =
    .ok v { s with regs := wX_update_regs r v s.regs } := by
  unfold rX_bits rX regval_from_reg wX_update_regs regval_into_reg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, bind, pure]
  obtain ⟨i⟩ := r
  have hne : i ≠ 0 := fun h => hr (by subst h; rfl)
  have hi : i.toNat < 32 := i.isLt
  have hcases : i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by
      have : i.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
      omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (
    simp only [h]
    simp only [readReg_insert_self, EStateM.bind, EStateM.pure])

-- If you write v to r to update state to s' and then read r state does not change 
-- and you get back v
-- NOTE: You do not need well formed here as r is guaranteed to be populated.
theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hr : r ≠ regidx.Regidx 0)
    (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by
  have ⟨s'', h_ok, h_regs⟩ := wX_regs_spec r v s
  have ⟨_, heq⟩ := eStateM_deterministic hw h_ok; subst heq
  have h_mod := wX_eq_modify_regs r v s s' hw
  rw [h_mod, h_regs]
  exact rX_after_wX r v s hr

-- ============================================================================
-- stateAfterWrite: pure model of a register write's effect on SailState
-- ============================================================================
noncomputable def stateAfterWrite (s : SailState) (rd : regidx) (val : BitVec 64) : SailState :=
  { s with regs := wX_update_regs rd val s.regs }

/-- The pure write model leaves the Sail state unchanged when the destination
is architectural register `x0`. -/
theorem stateAfterWrite_regidx_zero (s : SailState) (val : BitVec 64) :
    stateAfterWrite s (regidx.Regidx 0) val = s := by
  unfold stateAfterWrite wX_update_regs
  rfl

theorem stateAfterWrite_stateAfterWrite (rd : regidx) (v1 v2 : BitVec 64) (s : SailState) :
    stateAfterWrite (stateAfterWrite s rd v1) rd v2 = stateAfterWrite s rd v2 := by
  unfold stateAfterWrite
  simp only [wX_update_regs_idem]

theorem rX_after_stateAfterWrite (rd : regidx) (v : BitVec 64) (s : SailState)
    (hrd : rd ≠ regidx.Regidx 0) :
    rX_bits rd (stateAfterWrite s rd v) = .ok v (stateAfterWrite s rd v) := by
  unfold stateAfterWrite
  exact rX_after_wX rd v s hrd

-- StateAfterWrite changes only rd with value v 
theorem wX_bits_eq_stateAfterWrite (rd : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits rd v s = .ok () s') :
    s' = stateAfterWrite s rd v := by
  unfold stateAfterWrite
  have ⟨s'', h_ok, h_regs⟩ := wX_regs_spec rd v s
  have ⟨_, heq⟩ := eStateM_deterministic hw h_ok; subst heq
  have hmod := wX_eq_modify_regs rd v s s' hw
  rw [hmod, h_regs]

end
