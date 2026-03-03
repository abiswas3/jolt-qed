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

Since the program counter is not modeled in State, neither the RISC-V
MRET nor the Jolt JALR (with rd=0) modify any observable state
(registers, memory, CSRs, error flag). Both are identity on State.
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- RISC-V MRET: jump to mepc. No observable state change (PC not modeled). -/
def Riscv.mret (s : State) : State := s

/-- Jolt decomposition of MRET: JALR rd=0, rs1=mepc_vr, imm=0.
    With rd=0 the link-register write is suppressed, so no state change. -/
def jolt_mret (s : State) : State := s

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem mret_eq (s : State) :
    Riscv.mret s = jolt_mret s := rfl
