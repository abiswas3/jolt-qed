import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# CSRRW: RISC-V ≡ Jolt Decomposition

## Instruction (RV64 Zicsr, Format I)

`CSRRW rd, csr, rs1` atomically reads the CSR into rd and writes rs1 to the CSR.
- If rd = x0, the read is suppressed (write-only).
- If rd = rs1, a temporary is used to preserve the original rs1.

## Jolt Decomposition (faithful to Rust implementation)

Jolt maps each CSR to a virtual register. The inline sequence depends on
the operand pattern:

### Case 1: rd = 0 (write-only, `csrw` pseudo-op)
```
ADDI    csr_vreg, rs1, 0              -- csr ← rs1
```

### Case 2: rd = rs1 (same register)
```
ADDI    v_tmp, rs1, 0                 -- save rs1 in temp
ADDI    rd, csr_vreg, 0               -- rd ← old csr value
ADDI    csr_vreg, v_tmp, 0            -- csr ← saved rs1
```

### Case 3: rd ≠ rs1 (general case)
```
ADDI    rd, csr_vreg, 0               -- rd ← old csr value
ADDI    csr_vreg, rs1, 0              -- csr ← rs1
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
-- For now, we parameterize over the CSR virtual register index.

-- ============================================================================
-- RISC-V CSRRW definition (state-level, sorry)
-- ============================================================================

-- CSRRW requires CSR state modeling beyond the current State.
-- Placeholder: the pure-function equivalence cannot be expressed as a
-- simple FormatI op because CSRRW reads AND writes a CSR register
-- (two register writes per instruction).

-- ============================================================================
-- Main theorems (sorry stubs)
-- ============================================================================

-- TODO: Define Riscv.csrrw and csrrwJolt once CSR state is modeled.
-- The proof structure will follow the same pattern:
--   1. Unfold both definitions
--   2. Case split on rd = 0, rd = rs1, rd ≠ rs1
--   3. Show register file equality in each case
-- theorem csrrw_eq : ... := by sorry
