/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ADVICELW: RISC-V ≡ Jolt Decomposition

## Instruction (Jolt virtual)

`ADVICELW` loads 4 bytes from the advice tape and sign-extends to 64 bits.

## Jolt Decomposition (64-bit)

1. `VirtualAdviceLoad rd, 4` — zero-extends word to 64 bits
2. `SLLI rd, rd, 32`
3. `SRAI rd, rd, 32`

## Proof

Shift-based sign extension (SLLI 32 + SRAI 32) equals `signExtend 64`
for a 32-bit value.
-/

-- ============================================================================
-- Sign-extension lemma
-- ============================================================================

lemma sshiftRight_slli_signExtend_32 (x : BitVec 32) :
    (x.setWidth 64 <<< 32).sshiftRight 32 = x.signExtend 64 := by
  bv_decide

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Jolt decomposition of ADVICELW: VirtualAdviceLoad + SLLI 32 + SRAI 32. -/
def jolt_advicelw (rd : BitVec 5) (advice : BitVec 32) (s : State) : State :=
  let val := advice.setWidth 64
  let val := (val <<< 32).sshiftRight 32
  { s with reg := write rd val s.reg }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem advicelw_eq (rd : BitVec 5) (advice : BitVec 32) (s : State) :
    Riscv.advicelw rd advice s = jolt_advicelw rd advice s := by
  simp only [Riscv.advicelw, jolt_advicelw, sshiftRight_slli_signExtend_32]
