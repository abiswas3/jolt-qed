
# Jolt-QED: State of the World

This project proves Jolt bytecode expansions are equivalent to RISC-V
instructions as specified by the Sail formal model.

## Proof philosophy

1. **Main theorems must pass.** Helper lemmas can be sorry'd.
2. **Break proofs into simple lemmas.** Never prove a complex thing directly.
   The deeper you go, the purer the math becomes. Monadic plumbing at the
   top, pure BitVec identities at the bottom.
3. **Leverage Mathlib.** Before writing any proof, search Mathlib for existing
   lemmas. The smaller the fact, the more likely it already exists.
4. **Always check BytecodeExpansions/Instructions/ for the actual Jolt
   decomposition.** Never invent decompositions — use what Jolt really does.
5. **English descriptions on every theorem.** What does it say, why does it matter.

## Architecture

Three layers, each with a different state model:

### 1. BytecodeExpansions/ (pure-function equivalence, 65 instructions)

Simple `State` record (`reg : BitVec 5 → BitVec 64`, `mem : BitVec 64 → BitVec 8`).
Proves `Riscv.X = JoltX` as pure functions. No monads, no Sail.

### 2. SailJoltState/ (manual monadic proofs, 5 instructions)

Field-duplication `SailJoltState`. Manual `sail_cases` plumbing.
Proves `projectResult (jolt.run js) = sail.run (project js)`.

### 3. EmbeddedSailJoltState/ (mvcgen proofs, 9 instructions)

Embedded `SailJoltState` with `sail : SailState`. `@[spec]` Hoare triples +
`mvcgen` automates monadic plumbing. `WellFormed` (registers initialized) and
`JoltConfig` (M-mode, flat memory) as preconditions.

## Instruction status (EmbeddedSailJoltState/)

### Fully proved (zero sorries, including all helpers)

| Instruction | Jolt decomposition |
|---|---|
| ADDW | `execute_RTYPE ADD` + VSEW |
| SUBW | `execute_RTYPE SUB` + VSEW |
| ADDIW | `execute_ITYPE ADDI` + VSEW |
| SRAI | read rs1 + sshiftRight(ctz(bitmask)) + write rd |
| SRAIW | VSEW→vreg + VirtualSRAI→rd + VSEW (3-step) |
| SRAW | VSEW + ANDI 0x1f + bitmask + VirtualSRA + VSEW (5-step) |

### Main theorem proved, helper lemmas sorry'd

| Instruction | Jolt decomposition | Sorry'd helpers |
|---|---|---|
| SLLW | VirtualPow2W + MUL + VSEW | Transitive sorry in BytecodeExpansions (`sll_32_eq_mul_trunc`) |
| SRLW | SLLI 32 + bitmask + VirtualSRL + VSEW | `srlw_shift_eq`: `(x <<< 32 >>> (s+32)).setWidth 32 = x.setWidth 32 >>> s` |
| LW | ADDI + ANDI + LD + SLLI + SRL + VSEW | 3 memory helpers + 2 vmem_read bridge |

### Sorry decomposition (deepest sorries are pure math)

```
jolt_srlw_eq_sail              ← PROVED (no sorry)
  └── srlw_shift_eq            ← sorry (BitVec identity)
        decomposes into:
        ├── (x <<< n >>> (n+s)) = x >>> s           ← pure BitVec (search Mathlib)
        └── (x >>> s).setWidth k = x.setWidth k >>> s  ← pure BitVec (search Mathlib)

jolt_sllw_eq_sail              ← PROVED (no sorry in our file)
  └── sllw_eq_sllwJolt         ← from BytecodeExpansions (transitive sorry)
        └── sll_32_eq_mul_trunc ← sorry: x.setWidth 32 <<< s = (x * 2^s).setWidth 32

jolt_lw_eq_sail                ← PROVED (no sorry)
  ├── execute_LOAD_LW_factored ← sorry (vmem_read pipeline collapse under JoltConfig)
  │     └── translateAddr_machine_bare ← sorry (Machine mode → Bare translation)
  │           decomposes into: readReg lemmas + effectivePrivilege + translationMode
  ├── sailReadDword_ok         ← sorry (mem reads succeed under mem_populated)
  ├── sailReadWord_ok          ← sorry (same)
  └── sailReadWord_eq_dword_extract ← sorry (dword >>> shift = word, pure byte math)
```

## File structure

```
EmbeddedSailJoltState/
  Defs.lean             -- SailJoltState, liftSail, memory primitives, JoltConfig
  RegisterOps.lean      -- register lemmas, stateAfterWrite
  RtypeW.lean           -- @[spec] Hoare triples, generic W-type framework
  InstructionEquivalence/
    Addw.lean           -- ADDW (fully proved)
    Subw.lean           -- SUBW (fully proved)
    Addiw.lean          -- ADDIW (fully proved)
    Srai.lean           -- SRAI (fully proved)
    Sraiw.lean          -- SRAIW (fully proved)
    Sraw.lean           -- SRAW (fully proved)
    Sllw.lean           -- SLLW (main proved, transitive sorry)
    Srlw.lean           -- SRLW (main proved, 1 math sorry)
    Lw.lean             -- LW (main proved, 5 sorry'd helpers)
```

## What remains

### Immediate (pure math, no framework work)
- Prove `srlw_shift_eq` by decomposing into Mathlib BitVec lemmas
- Prove `sll_32_eq_mul_trunc` in BytecodeExpansions
- Prove `sailReadWord_ok` / `sailReadDword_ok` (unfold to mem.get?)
- Prove `sailReadWord_eq_dword_extract` (port from BytecodeExpansions/Lw.lean)

### Medium (Sail model reasoning)
- Prove `translateAddr_machine_bare` (readReg + effectivePrivilege + translationMode)
- Prove `execute_LOAD_LW_factored` (full vmem_read pipeline)

### New instructions (framework handles the plumbing)
- SLL, SRL, SRA — read-compute-write, primitive specs
- SLLI, SRLI — like SRAI
- SLLIW, SRLIW — like SRAIW
- MUL, MULW, MULH, MULHSU — new Sail functions, same pattern
- Loads (LB, LBU, LH, LHU, LWU, LD) — same bridge as LW
- Stores (SB, SH, SW) — need vmem_write bridge
- Atomics, CSR, System — more complex Sail semantics
