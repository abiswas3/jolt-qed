# JoltBytecode

Formal verification of [Jolt](https://github.com/a16z/jolt)'s RISC-V bytecode expansion equivalences in [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

> [!WARNING]
> This project uses `leanprover/lean4:v4.29.0-rc4` to be compatible with both Mathlib and [lean-sail](https://github.com/rems-project/lean-sail) (v3). The lean-sail dependency targets `nightly-2026-03-05`, but that nightly has no cached Mathlib build. We use `v4.29.0-rc4` as the closest stable toolchain with Mathlib cache available. Lean-sail compiles cleanly under this toolchain despite the minor version mismatch.

## Sail ↔ Jolt Instruction Equivalences (EmbeddedSailJoltState/)

Each theorem proves: `projectResult (jolt_X.run js) = sail_X.run js.sail` — running Jolt's bytecode decomposition and projecting onto Sail state equals running the native Sail RISC-V instruction directly.

## Misaligned memory accesses: why we changed the Sail platform flag

Jolt's inline memory instructions do not implement native split misaligned loads or stores. 
They compute an effective address `ea := rs1 + sext(imm)`, check the required alignment for the access width, and if the address is misaligned they stop immediately with an alignment failure instead of continuing through a split memory-read or memory-write path. 
This is the intended Jolt behavior for the load family we are verifying: `LB`, `LBU`, `LH`, `LHU`, `LW`, and `LWU`, and the same issue will apply to stores as we formalize them.

By contrast, a native RISC-V CPU may permit misaligned loads and stores. 
In the Sail model we imported, that behavior was enabled by default: ordinary misaligned accesses were allowed to continue through the virtual-memory pipeline rather than trapping immediately. 
TODO: Add a statement that EF requires this be default behaviour.
That created a semantic mismatch. 
Jolt stopped immediately on a misaligned memory access, but Sail's `execute_LOAD` / `execute_STORE` pipeline kept going. 
Under that configuration, the two machines are not definitionally equivalent on the misaligned branch, so the equivalence theorem cannot be proved in the form we want.

To make the equivalence theorems match Jolt's behavior, we changed the transpiled Sail platform constant:

```lean
-- WARNING: CHANGE IN TRANSPILED CODE
def plat_enable_misaligned_access : Bool := false
```

This was changed in the transpiled platform file:
- [RiscvPlatform.lean](./.lake/packages/Lean_RV64D/LeanRV64D/RiscvPlatform.lean)

The reason this suffices is that the misaligned behavior in the Sail memory path is controlled by a single boolean guard. 
For loads, the relevant chain is:

1. `execute_LOAD imm rs1 rd is_unsigned width`
2. `vmem_read rs1 offset width (Load Data) false false false`
3. `ext_data_get_addr rs1 offset ...`
4. `vmem_read_addr vaddr offset width ...`
5. `access_causes_misaligned_exception vaddr width res`

The key definition is:

```lean
def access_causes_misaligned_exception (vaddr : virtaddr) (width : Nat) (must_be_aligned : Bool) : Bool :=
  ((not (is_aligned_vaddr vaddr width)) && ((not plat_enable_misaligned_access) || must_be_aligned))
```

When `plat_enable_misaligned_access = true`, an ordinary access with `must_be_aligned = false` does **not** raise the misalignment exception just from being unaligned. 
The guard becomes false, and Sail proceeds into the rest of `vmem_read_addr` / `vmem_write_addr`, where it can split the access and continue the memory operation.

When `plat_enable_misaligned_access = false`, the same guard becomes true exactly when the address is not aligned. Then `vmem_read_addr` takes its early-exit branch:

```lean
if access_causes_misaligned_exception vaddr width res
then pure (Err (Memory_Exception (vaddr, E_Load_Addr_Align ())))
else ...
```

That `Err` is then propagated back up unchanged:

- `vmem_read_addr` returns `Err (Memory_Exception ...)`
- `vmem_read` returns the same `Err`
- `execute_LOAD` matches on the result and returns `pure e`

So after this platform change, Sail returns the same immediate alignment exception that Jolt returns on the misaligned branch, instead of silently continuing via split accesses.

### Fully proved (zero sorries)

**TODO:** currently stale.

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
