import JoltBytecode.JoltISA.Environment

/-!
# `SailJoltState` bookkeeping lemmas

These lemmas are about the virtual-register component of `SailJoltState`.
They are not instruction-specific and do not belong to any instruction
equivalence family.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-- After writing `v` to vreg `vd`, the lookup at `vd` returns `v`. -/
theorem vregs_write_self (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs vd
      = v := by
  show (if vd = vd then v else js.vregs vd) = v
  rw [if_pos rfl]

/-- After writing `v` to vreg `vd`, other vregs are preserved. -/
theorem vregs_write_pres (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64)
    (k : BitVec 7) (h : k ≠ vd) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs k
      = js.vregs k := by
  show (if k = vd then v else js.vregs k) = js.vregs k
  rw [if_neg h]

/-- Chain four virtual-register preservation hypotheses. -/
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

/-- Chain three virtual-register preservation hypotheses. -/
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

end
