import LeanRV64D

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
## Load-halfword vs load-word + shift-right equivalence

  LHS:  lhu  r1, [r4+2]          — unsigned halfword load from address r4+2
  RHS:  lwu  r1, [r4]            — unsigned word load from address r4
        srli r1, r1, 16          — then logical right shift by 16

Both extract bits [31:16] of the 32-bit word at r4 (little-endian),
zero-extended to 64 bits.
-/

abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- ═══════════════════════════════════════════════════════════
-- LHS: a single halfword load — LHU r1, 2(r4)
-- ═══════════════════════════════════════════════════════════

def loadh (r1 r4 : regidx) : SailM ExecutionResult :=
  execute_LOAD (2 : BitVec 12) r4 r1 true 2

-- ═══════════════════════════════════════════════════════════
-- RHS: word load then shift — LWU r1, 0(r4)  ;  SRLI r1, r1, 16
-- ═══════════════════════════════════════════════════════════

def lwu_then_srli (r1 r4 : regidx) : SailM (ExecutionResult × ExecutionResult) := do
  let r₁ ← execute_LOAD (0 : BitVec 12) r4 r1 true 4
  let r₂ ← execute_SHIFTIOP (16 : BitVec 6) r1 r1 sop.SRLI
  pure (r₁, r₂)

-- ═══════════════════════════════════════════════════════════
-- Theorem: the final states agree
-- ═══════════════════════════════════════════════════════════

theorem loadh_eq_lwu_srli (r1 r4 : regidx) (s s_lhs s_rhs : SailState)
    (h_lhs : loadh r1 r4 s = .ok RETIRE_SUCCESS s_lhs)
    (h_rhs : lwu_then_srli r1 r4 s = .ok (RETIRE_SUCCESS, RETIRE_SUCCESS) s_rhs) :
    s_lhs = s_rhs := by
  sorry

end
