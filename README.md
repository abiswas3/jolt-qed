# JoltBytecode

Formal verification of [Jolt](https://github.com/a16z/jolt)'s RISC-V bytecode expansion equivalences in [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

## Overview

Jolt is a zkVM that replaces complex RISC-V instructions with sequences of simpler virtual instructions. For soundness, each replacement sequence must compute the exact same result as the original instruction.

This repository contains machine-checked proofs in Lean 4 that each Jolt bytecode expansion is equivalent to its corresponding RISC-V instruction.

## Verified Instructions

✅ : Complete
⏳ : In Progress

| Instruction | RISC-V Description | Status | Proof |
|---|---|---|---|
| `MULH` | Signed high multiplication | ✅ | [`BytecodeExpansions/Mulh.lean`](JoltBytecode/BytecodeExpansions/Mulh.lean) |
| `SUBW` |  | ✅ | [`BytecodeExpansions/SUBW.lean`](JoltBytecode/BytecodeExpansions/SUBW.lean) |

> More instructions will be added as proofs are completed.

## Project Structure

```
JoltBytecode/
├── lakefile.lean                          # Lake build configuration
├── lean-toolchain                         # Lean version pin
├── JoltBytecode.lean                      # Root import (imports all modules)
└── JoltBytecode/
    └── BytecodeExpansions/
        └── Mulh.lean                      # MULH ≡ MULH_JOLT proof
```

## Building

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Build

```bash
# Fetch Mathlib and dependencies (first time only, takes a while)
lake update

# Download pre-built Mathlib .olean cache (highly recommended)
lake exe cache get

# Build all proofs
lake build
```

A successful `lake build` with no errors means every theorem in the repository has been machine-checked by the Lean kernel.

## Proof Strategy

Each bytecode expansion proof follows a common pattern:

1. **Define** the original RISC-V instruction semantics (e.g., `mulh`)
2. **Define** the Jolt virtual instruction decomposition (e.g., `mulhJolt`)
3. **Prove** equivalence: the original and decomposed versions produce identical `BitVec w` results for all inputs

### MULH Example

The RISC-V `MULH rd, rs1, rs2` computes the upper *w* bits of the signed product. Jolt replaces it with:

```
VirtualMovsign  v_sx, rs1, 0      -- s_x = sign(rs1)
VirtualMovsign  v_sy, rs2, 0      -- s_y = sign(rs2)
MULHU           v_0,  rs1, rs2    -- unsigned high multiply
MUL             v_sx, v_sx, rs2   -- sign correction term 1
MUL             v_sy, v_sy, rs1   -- sign correction term 2
ADD             v_0,  v_0,  v_sx  -- accumulate
ADD             rd,   v_0,  v_sy  -- final result
```


## Adding a New Proof

1. Create a new file in `JoltBytecode/BytecodeExpansions/`, e.g., `Mulhu.lean`
2. Define both the RISC-V instruction and the Jolt decomposition
3. Prove equivalence
4. Add the import to `JoltBytecode.lean`:
   ```lean
   import JoltBytecode.BytecodeExpansions.Mulhu
   ```
5. Run `lake build` to verify

## References

- [Jolt](https://github.com/a16z/jolt) - The Jolt zkVM implementation
- [Jolt DOcs]() - Documentation and specification (**In Progress**)
- [RISC-V ISA specification](https://riscv.org/technical/specifications/) - Instruction semantics
- [Mathlib4](https://github.com/leanprover-community/mathlib4) - Lean 4 math library

## License

Apache-2.0. See [LICENSE](LICENSE).
