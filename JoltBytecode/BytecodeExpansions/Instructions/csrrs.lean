/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# CSRRS: RISC-V ≡ Jolt Decomposition

## Instruction (RV64 Zicsr, Format I)

`CSRRS rd, csr, rs1` reads the CSR into rd. If rs1 ≠ x0, sets (ORs) the
bits of rs1 into the CSR.

## Jolt Decomposition (faithful to Rust implementation)

Jolt maps each CSR to a virtual register. The inline sequence depends on
the operand pattern:

### Case 1: rs1 = 0 (read-only, `csrr` pseudo-op)
```
ADDI    rd, csr_vreg, 0               -- rd ← csr value
```

### Case 2: rd = 0 (set-only)
```
ORI     csr_vreg, csr_vreg, rs1       -- csr ← csr | rs1
```

### Case 3: rd = rs1 (same register)
```
ADDI    v_tmp, csr_vreg, 0            -- save csr in temp
ORI     csr_vreg, csr_vreg, rs1       -- csr ← csr | rs1
ADDI    rd, v_tmp, 0                  -- rd ← old csr value
```

### Case 4: rd ≠ rs1 (general case)
```
ADDI    rd, csr_vreg, 0               -- rd ← old csr value
ORI     csr_vreg, csr_vreg, rs1       -- csr ← csr | rs1
```

## Note

This proof requires modeling CSR registers in the state. The current State
model only has general-purpose registers and memory. A CSR extension is
needed before this proof can be completed.

## Supported CSRs
- CSR_MSTATUS, CSR_MTVEC, CSR_MSCRATCH, CSR_MEPC, CSR_MCAUSE, CSR_MTVAL
-/

-- ============================================================================
-- CSR virtual register mapping (placeholder)
-- ============================================================================

-- In Jolt, CSRs are mapped to virtual register addresses.
-- This would need to be defined based on the actual Jolt CSR allocation.

-- ============================================================================
-- Main theorems (sorry stubs)
-- ============================================================================

-- TODO: Define Riscv.csrrs and csrrsJolt once CSR state is modeled.
-- CSRRS reads one register (CSR) and conditionally writes another,
-- so it cannot be expressed as a pure FormatI op.
-- The proof structure will:
--   1. Case split on rs1 = 0, rd = 0, rd = rs1, general
--   2. Show register file equality in each case
-- theorem csrrs_eq : ... := by sorry
