/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ADVICELH: RISC-V ≡ Jolt Decomposition

## Instruction (Jolt virtual)

`ADVICELH` loads 2 bytes from the advice tape and sign-extends to 64 bits.

## Jolt Decomposition (64-bit)

1. `VirtualAdviceLoad rd, 2` — zero-extends halfword to 64 bits
2. `SLLI rd, rd, 48`
3. `SRAI rd, rd, 48`

## Proof

Shift-based sign extension (SLLI 48 + SRAI 48) equals `signExtend 64`
for a 16-bit value.
-/

-- ============================================================================
-- Sign-extension lemma
-- ============================================================================

lemma sshiftRight_slli_signExtend_16 (x : BitVec 16) :
    (x.setWidth 64 <<< 48).sshiftRight 48 = x.signExtend 64 := by
  bv_decide

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Jolt decomposition of ADVICELH: VirtualAdviceLoad + SLLI 48 + SRAI 48. -/
def jolt_advicelh (rd : BitVec 5) (advice : BitVec 16) (s : State) : State :=
  let val := advice.setWidth 64
  let val := (val <<< 48).sshiftRight 48
  { s with reg := write rd val s.reg }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem advicelh_eq (rd : BitVec 5) (advice : BitVec 16) (s : State) :
    Riscv.advicelh rd advice s = jolt_advicelh rd advice s := by
  simp only [Riscv.advicelh, jolt_advicelh, sshiftRight_slli_signExtend_16]
