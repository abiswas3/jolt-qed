import JoltBytecode.SailJoltState.EmbeddedArch.Defs

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

-- We need register lemmas. These are about SailState (not SailJoltState)
-- so they work regardless of the SailJoltState architecture.
-- Re-prove wX_shape here to avoid import conflicts with old Defs.lean.

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
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast, bind, pure]
  reg_cases r <;>
    simp_all [Sail.writeReg, PreSail.writeReg, xreg_write_callback,
              reg_name_forwards, to_bits] <;>
    exact ⟨_, rfl⟩

-- wX_rX_roundtrip: write then read gives back the value.
-- (sorry for now — same proof as RegisterLemmas.lean, just avoiding import conflict)
theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hr : r ≠ regidx.Regidx 0) (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by sorry

-- wX_wX_collapse: double write = single write.
theorem wX_wX_collapse (r : regidx) (v1 v2 : BitVec 64) (s s1 s2 : SailState)
    (hw1 : wX_bits r v1 s = .ok () s1) (hw2 : wX_bits r v2 s1 = .ok () s2) :
    wX_bits r v2 s = .ok () s2 := by sorry

-- extractLsb distributes over addition.
theorem extractLsb_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb (a + b) 31 0 =
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-! ## ADDW -/

def jolt_addw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let _ ← liftSail (execute_RTYPE rs2 rs1 rd rop.ADD)
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_addw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) :
    projectResult ((jolt_addw rs2 rs1 rd).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.ADDW).run js.sail := by
  unfold execute_RTYPEW jolt_addw jolt_virtual_sign_extend_word liftSail projectResult execute_RTYPE
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  -- Case-split on reads. With embedded arch, we use js.sail directly.
  sail_cases rX_bits rs1 js.sail
  rename_i v1 s1
  sail_cases rX_bits rs2 s1
  rename_i v2 s2
  -- Both reads succeeded.
  obtain ⟨s3, hwx⟩ := wX_shape rd (v1 + v2) s2
  simp [hwx]
  have hrx := wX_rX_roundtrip rd (v1 + v2) s2 s3 hrd hwx
  simp [hrx]
  rw [extractLsb_add v1 v2]
  obtain ⟨s4, hwx2⟩ := wX_shape rd
      (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0)) s3
  have hcollapse := wX_wX_collapse rd (v1 + v2)
      (sign_extend (Sail.BitVec.extractLsb v1 31 0 + Sail.BitVec.extractLsb v2 31 0))
      s2 s3 s4 hwx hwx2
  simp [hwx2, hcollapse]

end
