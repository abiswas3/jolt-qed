# JoltBytecode

Formal verification of [Jolt](https://github.com/a16z/jolt)'s RISC-V bytecode expansion equivalences in [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

> [!WARNING]
> This project uses `leanprover/lean4:v4.29.0-rc4` to be compatible with both Mathlib and [lean-sail](https://github.com/rems-project/lean-sail) (v3). The lean-sail dependency targets `nightly-2026-03-05`, but that nightly has no cached Mathlib build. We use `v4.29.0-rc4` as the closest stable toolchain with Mathlib cache available. Lean-sail compiles cleanly under this toolchain despite the minor version mismatch.

## Sail ↔ Jolt Instruction Equivalences (EmbeddedSailJoltState/)

Each theorem proves: `projectResult (jolt_X.run js) = sail_X.run js.sail` — running Jolt's bytecode decomposition and projecting onto Sail state equals running the native Sail RISC-V instruction directly.

### Fully proved (zero sorries)

| Instruction | Jolt decomposition | Status |
|---|---|---|
| ADDW | `execute_RTYPE ADD` + VSEW | **Proved** |
| SUBW | `execute_RTYPE SUB` + VSEW | **Proved** |
| ADDIW | `execute_ITYPE ADDI` + VSEW | **Proved** |
| SRAI | read rs1 + sshiftRight(ctz(bitmask)) + write rd | **Proved** |
| SRAIW | VSEW→vreg + VirtualSRAI→rd + VSEW (3-step) | **Proved** |

### Main theorem proved, helper lemmas sorry'd

| Instruction | Jolt decomposition | Sorry'd helpers |
|---|---|---|
| SLLW | VirtualPow2W + MUL + VSEW | `sllw_mul_eq_shift` (BitVec math) |
| SRLW | SLLI 32 + bitmask + VirtualSRL + VSEW | `srlw_shift_eq` (BitVec math) |
| SRAW | VSEW + ANDI 0x1f + bitmask + VirtualSRA + VSEW | `sraw_five_step_value` (BitVec math) |
| LW | ADDI + ANDI + LD + SLLI + SRL + VSEW | 3 memory helpers + 2 vmem_read bridge |

### Not yet started (pure-function proofs exist in BytecodeExpansions/)

#### Shift instructions
| Instruction | Type | Notes |
|---|---|---|
| SLL | R-type | Primitive specs (read-compute-write) |
| SRL | R-type | Primitive specs |
| SRA | R-type | Primitive specs |
| SLLI | I-type shift | Like SRAI |
| SRLI | I-type shift | Like SRAI |
| SLLIW | I-type shift W | Like SRAIW |
| SRLIW | I-type shift W | Like SRAIW |

#### Multiply / Divide
| Instruction | Type | Notes |
|---|---|---|
| MUL | `execute_MUL` | New Sail function, read-compute-write |
| MULW | `execute_MULW` | Read, truncate, multiply, sign-extend |
| MULH | `execute_MUL` | Upper-half multiply |
| MULHSU | `execute_MUL` | Signed×unsigned upper-half |
| DIV | | |
| DIVU | | |
| DIVW | | |
| DIVUW | | |
| REM | | |
| REMU | | |
| REMW | | |
| REMUW | | |

#### Load / Store (need memory bridge — `JoltConfig` + `vmem_read` pipeline)
| Instruction | Type | Notes |
|---|---|---|
| LB | Load byte | Same bridge as LW, width=1 |
| LBU | Load byte unsigned | Same bridge, unsigned extend |
| LH | Load halfword | Same bridge, width=2 |
| LHU | Load halfword unsigned | Same bridge, unsigned extend |
| LWU | Load word unsigned | Same bridge, unsigned extend |
| LD | Load doubleword | Same bridge, width=8 |
| SB | Store byte | Need `vmem_write` bridge |
| SH | Store halfword | Need `vmem_write` bridge |
| SW | Store word | Need `vmem_write` bridge |

#### Atomic (need memory bridge + atomics)
| Instruction | Notes |
|---|---|
| AMOADDD, AMOADDW | Atomic add |
| AMOANDD, AMOANDW | Atomic and |
| AMOMAXD, AMOMAXUD, AMOMAXUW, AMOMAXW | Atomic max |
| AMOMIND, AMOMINUD, AMOMINUW, AMOMINW | Atomic min |
| AMOORD, AMOORW | Atomic or |
| AMOSWAPD, AMOSWAPW | Atomic swap |
| AMOXORD, AMOXORW | Atomic xor |
| LRD, LRW | Load reserved |
| SCD, SCW | Store conditional |

#### Advice / System / CSR
| Instruction | Notes |
|---|---|
| ADVICELB, ADVICELD, ADVICELH, ADVICELW | Jolt advice instructions |
| CSRRS, CSRRW | CSR read/write |
| ECALL | Environment call |
| MRET | Machine return |

## Pure-function equivalences (BytecodeExpansions/)

65 instructions proved at the pure-function level using a simplified state model (`State` with `reg : BitVec 5 → BitVec 64`, `mem : BitVec 64 → BitVec 8`). These prove `Riscv.X = JoltX` as pure functions, without monadic state or the Sail model.

## Manual monadic proofs (SailJoltState/)

5 instructions proved with manual monadic plumbing (field-duplication architecture, no `WellFormed` assumption). These are the original proofs before the mvcgen framework was developed. Independent from EmbeddedSailJoltState/ — zero cross-imports.
