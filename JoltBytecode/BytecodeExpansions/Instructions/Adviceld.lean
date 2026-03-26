/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ADVICELD: RISC-V ≡ Jolt Decomposition

## Instruction (Jolt virtual)

`ADVICELD` loads 8 bytes from the advice tape into rd (no sign extension).

## Jolt Decomposition (64-bit)

1. `VirtualAdviceLoad rd, 8` — loads 8 bytes directly

## Proof

Both sides write the advice value directly to rd. `rfl`.
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Jolt decomposition of ADVICELD: VirtualAdviceLoad (8 bytes, no sign extension). -/
def jolt_adviceld (rd : BitVec 5) (advice : BitVec 64) (s : State) : State :=
  { s with reg := write rd advice s.reg }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem adviceld_eq (rd : BitVec 5) (advice : BitVec 64) (s : State) :
    Riscv.adviceld rd advice s = jolt_adviceld rd advice s := rfl
