import JoltBytecode.SailJoltState.Common

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- readReg after inserting the same key returns the inserted value.
theorem readReg_insert_self (reg : Register) (v : RegisterType reg) (s : SailState) :
    (PreSail.readReg reg : SailM (RegisterType reg))
      { s with regs := s.regs.insert reg v } =
    .ok v { s with regs := s.regs.insert reg v } := by
  unfold PreSail.readReg
  simp only [bind, get, getThe, EStateM.bind, EStateM.get, MonadStateOf.get,
             Std.ExtDHashMap.get?_insert_self, pure, EStateM.pure]

-- Factoring lemma for rX: reading register r from a state where
-- wX_update_regs r v was applied returns v. This avoids unfolding
-- the full wX_bits + rX_bits chain simultaneously.
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
    simp only [h]  -- substitute i.toNat = N to pick match branch
    simp only [readReg_insert_self, bind, EStateM.bind, pure, EStateM.pure])

-- After writing v to rd, reading rd gives v back (for rd ≠ x0).
theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hr : r ≠ regidx.Regidx 0)
    (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by
  have ⟨s'', h_ok, h_regs⟩ := wX_regs_spec r v s
  have ⟨_, heq⟩ := eStateM_deterministic hw h_ok; subst heq
  have h_mod := wX_eq_modify_regs r v s s' hw
  rw [h_mod, h_regs]
  exact rX_after_wX r v s hr

end
