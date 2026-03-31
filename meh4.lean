import LeanRV64D

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
## ADDW: Sail RISC-V spec ≡ Jolt decomposition

  LHS:  execute_RTYPEW rs2 rs1 rd ropw.ADDW
  RHS:  execute_RTYPE rs2 rs1 rd rop.ADD ; virtual_sign_extend_word rd

### Caveat

This file expresses Jolt's virtual instruction (VirtualSignExtendWord) directly
in `SailM` using `rX_bits`/`wX_bits`. This works for ADDW because **all operands
are real CPU registers** — no virtual temporaries are needed.

For instructions whose Jolt decomposition uses virtual registers (e.g. LW, SW,
most loads/stores), this approach does NOT generalise. Those will require an
extended state (`JoltSailState`) that wraps `SailState` with additional virtual
register storage and a `liftSail` mechanism. See memory for the full plan.
-/

abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- WARNING: This definition only works when rd is a real RISC-V register (regidx).
-- It will NOT work for Jolt virtual registers (indices ≥ 32). For the general
-- case we need the JoltSailState extension with liftSail.
def virtual_sign_extend_word (rd : regidx) : SailM Unit := do
  let v ← rX_bits rd
  wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0))

-- Jolt's ADDW decomposition: ADD then VirtualSignExtendWord
def jolt_addw (rs2 rs1 rd : regidx) : SailM ExecutionResult := do
  let _ ← execute_RTYPE rs2 rs1 rd rop.ADD
  virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

/-! ### Infrastructure lemmas (reused from meh.lean) -/

theorem rX_bits_shape (r : regidx) (s : SailState) :
    (∃ v, rX_bits r s = .ok v s) ∨
    (rX_bits r s = .error .Unreachable s) := by
  obtain ⟨i⟩ := r
  unfold rX_bits rX regval_from_reg Sail.readReg PreSail.readReg
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
             bind, EStateM.bind, pure, EStateM.pure,
             getThe, MonadStateOf.get, get,
             throw, throwThe, MonadExceptOf.throw]
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
    simp_all [zero_reg, EStateM.pure, EStateM.get, EStateM.bind] <;>
    (first | (cases s.regs.get? _ <;> simp_all [EStateM.pure, EStateM.throw]) | skip)

/-! ### Key lemma needed: write-read roundtrip

After `wX_bits rd v s = .ok () s'`, reading back gives `rX_bits rd s' = .ok v s'`.

This requires showing that Sail's `writeReg` (HashMap insert) followed by
`readReg` (HashMap lookup) on the same register returns the written value.
The 32-way case split on register index × HashMap roundtrip is computationally
expensive — needs a dedicated tactic or abstraction over the register bank. -/

theorem wX_rX_roundtrip (r : regidx) (v : BitVec 64) (s s' : SailState)
    (hw : wX_bits r v s = .ok () s') :
    rX_bits r s' = .ok v s' := by
      sorry

/-! ### Main theorem -/

-- The main theorem: RISC-V ADDW = Jolt's decomposition
-- Proof outline:
-- 1. Both sides read rs1, rs2 (via rX_bits_shape — reads preserve state)
-- 2. LHS: computes sign_extend(extractLsb(v1, 31, 0) + extractLsb(v2, 31, 0)), writes to rd
-- 3. RHS: writes (v1 + v2) to rd, reads it back, writes sign_extend(extractLsb(v1+v2, 31, 0))
-- 4. Math: extractLsb distributes over addition (truncation commutes with add)
-- 5. wX_rX_roundtrip: reading rd after writing returns the written value
-- 6. Double write to rd collapses — only final value matters for state
theorem jolt_addw_eq_riscv_addw (rs2 rs1 rd : regidx) :
    execute_RTYPEW rs2 rs1 rd ropw.ADDW = jolt_addw rs2 rs1 rd := by
  funext s
  unfold execute_RTYPEW jolt_addw execute_RTYPE virtual_sign_extend_word
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  sorry

end
