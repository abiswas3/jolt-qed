import LeanRV64D

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
## RISC-V ADD commutativity

`execute_RTYPE rs2 rs1 rd op` reads `rs1`, reads `rs2`, applies `op`, writes to `rd`.
For ADD, swapping the source operands yields the same computation because:
1. Register reads don't modify state (they commute)
2. `BitVec.add_comm`: `a + b = b + a`
-/

abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- A computation preserves state if the output state always equals the input
def preserves_state {α : Type} (m : SailM α) (s : SailState) : Prop :=
  (match m s with | .ok _ s' => s' = s | .error _ s' => s' = s)

-- ─── Lemma 1: readReg is a pure read ─────────────────────────

theorem readReg_preserves_state (r : Register) (s : SailState) :
    preserves_state (Sail.readReg r : SailM (RegisterType r)) s := by
  unfold preserves_state Sail.readReg PreSail.readReg
  simp only [getThe, MonadStateOf.get, get, EStateM.get, bind, EStateM.bind]
  cases h : s.regs.get? r <;>
    simp_all [pure, EStateM.pure, throwThe, MonadExceptOf.throw, throw, EStateM.throw]

-- ─── Helper: readReg result shape ─────────────────────────

theorem readReg_shape (r : Register) (s : SailState) :
    (∃ v, (Sail.readReg r : SailM (RegisterType r)) s = .ok v s) ∨
    ((Sail.readReg r : SailM (RegisterType r)) s = .error .Unreachable s) := by
  unfold Sail.readReg PreSail.readReg
  simp only [getThe, MonadStateOf.get, get, EStateM.get, bind, EStateM.bind]
  cases h : s.regs.get? r with
  | none => right; simp [throw, EStateM.throw, throwThe, MonadExceptOf.throw]
  | some v => left; exact ⟨v, by simp [pure, EStateM.pure]⟩

-- ─── Core lemma: rX_bits has a well-defined shape ─────────────

-- rX_bits r s either succeeds with .ok v s or fails with .error .Unreachable s
theorem rX_bits_shape (r : regidx) (s : SailState) :
    (∃ v, rX_bits r s = .ok v s) ∨
    (rX_bits r s = .error .Unreachable s) := by
  obtain ⟨i⟩ := r
  -- Unfold the full chain: rX_bits → rX → readReg (all the way to get?)
  unfold rX_bits rX regval_from_reg Sail.readReg PreSail.readReg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, EStateM.bind, pure, EStateM.pure,
             getThe, MonadStateOf.get, get,
             throw, throwThe, MonadExceptOf.throw]
  -- Now everything is fully reduced to s.regs.get? calls and Nat match.
  -- The goal should be about:
  --   match (match i.toNat with | 0 => .ok zero_reg s | k => match s.regs.get? xK with ...) with ...
  -- We need to enumerate the 32 values of i.toNat and case-split on get? for each.
  have hi : i.toNat < 32 := i.isLt
  -- Enumerate using omega
  have hcases : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 ∨
    i.toNat = 4 ∨ i.toNat = 5 ∨ i.toNat = 6 ∨ i.toNat = 7 ∨
    i.toNat = 8 ∨ i.toNat = 9 ∨ i.toNat = 10 ∨ i.toNat = 11 ∨
    i.toNat = 12 ∨ i.toNat = 13 ∨ i.toNat = 14 ∨ i.toNat = 15 ∨
    i.toNat = 16 ∨ i.toNat = 17 ∨ i.toNat = 18 ∨ i.toNat = 19 ∨
    i.toNat = 20 ∨ i.toNat = 21 ∨ i.toNat = 22 ∨ i.toNat = 23 ∨
    i.toNat = 24 ∨ i.toNat = 25 ∨ i.toNat = 26 ∨ i.toNat = 27 ∨
    i.toNat = 28 ∨ i.toNat = 29 ∨ i.toNat = 30 ∨ i.toNat = 31 := by omega
  -- For each case, simp_all reduces the Nat match, then case-split on get? result
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                     h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp_all [zero_reg, EStateM.pure, EStateM.get, EStateM.bind] <;>
    (first | (cases s.regs.get? _ <;> simp_all [EStateM.pure, EStateM.throw]) | skip)

-- ─── Lemma 2: rX_bits preserves state ─────────────────────────

theorem rX_bits_preserves_state (r : regidx) (s : SailState) :
    preserves_state (rX_bits r) s := by
  have h := rX_bits_shape r s
  unfold preserves_state
  cases h with
  | inl h => obtain ⟨v, hv⟩ := h; simp [hv]
  | inr h => simp [h]

-- ─── Lemma 3: rX_bits always fails with the same error ───────

theorem rX_bits_error_uniform (a b : regidx) (s : SailState)
    (ea eb : Error exception) (sa sb : SailState)
    (ha : rX_bits a s = .error ea sa) (hb : rX_bits b s = .error eb sb) :
    ea = eb := by
  have hsa := rX_bits_shape a s
  have hsb := rX_bits_shape b s
  cases hsa with
  | inl h => obtain ⟨v, hv⟩ := h; simp [hv] at ha
  | inr h =>
    cases hsb with
    | inl h' => obtain ⟨v, hv⟩ := h'; simp [hv] at hb
    | inr h' => rw [h] at ha; rw [h'] at hb; cases ha; cases hb; rfl

-- ─── Main theorem: ADD is commutative ────────────────────────
-- this is an example of how to prove theorems about Galois RISC-V CPU.
theorem execute_RTYPE_ADD_comm (a b rd : regidx) :
    execute_RTYPE a b rd rop.ADD = execute_RTYPE b a rd rop.ADD := by
  funext s
  unfold execute_RTYPE
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have ha := rX_bits_preserves_state a s
  have hb := rX_bits_preserves_state b s
  unfold preserves_state at ha hb
  match hca : rX_bits a s, ha with
  | .ok va _, ha =>
    match hcb : rX_bits b s, hb with
    | .ok vb _, hb =>
      simp [hca, hcb, ha, hb, BitVec.add_comm va vb]
    | .error _ _, hb =>
      simp [hcb, ha, hb]
  | .error ea _, ha =>
    match hcb : rX_bits b s, hb with
    | .ok _ _, hb =>
      simp [hca, ha, hb]
    | .error eb _, hb =>
      simp [ha, hb]
      exact rX_bits_error_uniform b a s eb ea _ _ hcb hca

end
