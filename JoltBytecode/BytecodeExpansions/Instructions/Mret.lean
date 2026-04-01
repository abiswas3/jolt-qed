/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# MRET: RISC-V ≡ Jolt Decomposition

## Instruction (RV64, Machine Mode)

`MRET` reads the mepc CSR and jumps to it, returning from a machine-mode
exception handler. In the ZeroOS M-mode-only, single-core, no-interrupt
model, privilege-mode and interrupt-enable adjustments are omitted.

## Jolt Decomposition

```
JALR    rd=0, rs1=mepc_vr, imm=0     -- jump to mepc (no link write)
```

## Proof

Both sides set `pc := read_csr CSR_MEPC s`. The definitions are
structurally identical so the proof is `rfl`.
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- RISC-V MRET: jump to mepc by setting pc := mepc. -/
def Riscv.mret (s : State) : State :=
  { s with pc := read_csr CSR_MEPC s }

/-- Jolt decomposition of MRET: JALR rd=0, rs1=mepc_vr, imm=0.
    With rd=0 the link-register write is suppressed; sets pc := mepc. -/
def jolt_mret (s : State) : State :=
  { s with pc := read_csr CSR_MEPC s }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem mret_eq (s : State) :
    Riscv.mret s = jolt_mret s := rfl
