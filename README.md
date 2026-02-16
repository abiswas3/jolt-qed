# JoltBytecode

Formal verification of [Jolt](https://github.com/a16z/jolt)'s RISC-V bytecode expansion equivalences in [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

## Overview
TODO: 

## Verified Instructions

+ Mulh
+ Subw 
+ Lw - In progress 

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
        ...
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

TODO:

## License

Apache-2.0. See [LICENSE](LICENSE).
