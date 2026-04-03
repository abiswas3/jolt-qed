import JoltBytecode.SailJoltState.RegisterOps

/-!
# Jolt-specific Operations

Virtual register read/write, the sail_cases tactic, and shared Jolt
instructions like jolt_virtual_sign_extend_word.

Virtual registers (vregs) exist only in JoltState, not in SailState.
They are used by Jolt's instruction decompositions as scratch space.
After projection (projectResult), vregs disappear — they don't affect
the Sail-level result.

sail_cases is a tactic for case-splitting on shared EStateM.Result
discriminants that appear on both sides of an equation.
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Virtual register operations
-- ============================================================================

-- Read the contents of a virtual register.
def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

-- Write a value to a virtual register.
def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

-- ============================================================================
-- sail_cases tactic
-- ============================================================================

-- sail_cases case-splits on a shared EStateM.Result term that appears on
-- both sides of an equation. After unfolding definitions, the goal often
-- has the form:
--
--   (match rX_bits rs1 s with | .ok v s' => ... | .error e s' => ...) =
--   (match rX_bits rs1 s with | .ok v s' => ... | .error e s' => ...)
--
-- Both sides share the same discriminant (rX_bits rs1 s). We need to
-- case-split on it so both sides reduce together.
--
-- How it works:
--   1. generalize t = _sc — replaces ALL occurrences of t with _sc
--   2. cases _sc — splits into .ok and .error
--   3. <;> simp — closes error branches (trivially equal) and
--      simplifies ok branches (reduces the next match)
syntax "sail_cases" term : tactic
macro_rules
  | `(tactic| sail_cases $t:term) => `(tactic|
      (generalize $t = _sc; cases _sc <;> simp))

-- ============================================================================
-- Shared Jolt instructions
-- ============================================================================

-- Virtual sign-extend-word: reads register rd, sign-extends the lower
-- 32 bits back to 64 bits, and writes the result back to rd.
-- This is Jolt's way of narrowing a 64-bit result to 32-bit semantics
-- for W-type instructions (ADDW, SUBW, etc.).
def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

end
