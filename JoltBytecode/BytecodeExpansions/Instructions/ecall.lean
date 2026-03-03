import JoltBytecode.BytecodeExpansions.Common.Riscv

/-!
# ECALL: RISC-V ≡ Jolt Decomposition

## Instruction (RV64, Machine Mode)

`ECALL` triggers an environment call exception. In M-mode-only (ZeroOS):
- Save current PC to `mepc`
- Set `mcause` to 11 (environment call from M-mode)
- Clear `mtval`
- Set MPP bits in `mstatus` (bits [12:11] = 3, i.e. M-mode)
- Jump to `mtvec`

## Jolt Decomposition

The Jolt decomposition performs the same CSR writes in the same order
and sets PC to mtvec, so the proof is `rfl`.
-/

-- ============================================================================
-- Definitions
-- ============================================================================

/-- Jolt decomposition of ECALL: same CSR writes + pc := mtvec. -/
def jolt_ecall (s : State) : State :=
  let s := write_csr CSR_MEPC s.pc s
  let s := write_csr CSR_MCAUSE 11#64 s
  let s := write_csr CSR_MTVAL 0#64 s
  let s := write_csr CSR_MSTATUS (read_csr CSR_MSTATUS s ||| (3#64 <<< 11)) s
  { s with pc := read_csr CSR_MTVEC s }

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem ecall_eq (s : State) :
    Riscv.ecall s = jolt_ecall s := rfl
