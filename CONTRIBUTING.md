
# Contributing
TODO: Change this 
Thank you for your interest in contributing to JoltBytecode.

## Adding a New Bytecode Expansion Proof

Each RISC-V instruction that Jolt decomposes into virtual instructions needs a corresponding equivalence proof. Here's how to add one:

### 1. Create the proof file

Create `JoltBytecode/BytecodeExpansions/<InstructionName>.lean` with:

```lean
import Mathlib.Tactic
import Mathlib.Data.BitVec

/-!
# <INSTRUCTION> Equivalence Theorem
Brief description of what this instruction does and how Jolt decomposes it.
-/

section <INSTRUCTION>

variable {w : Nat}

-- Define the original RISC-V instruction
def <instruction> (x y : BitVec w) : BitVec w := ...

-- Define the Jolt decomposition
def <instruction>Jolt (x y : BitVec w) : BitVec w := ...

-- Prove equivalence
theorem <instruction>_eq_<instruction>Jolt (x y : BitVec w) :
    <instruction> x y = <instruction>Jolt x y := by
  sorry -- replace with your proof

end <INSTRUCTION>
```

### 2. Register the module

Add the import to `JoltBytecode.lean`:

```lean
import JoltBytecode.BytecodeExpansions.<InstructionName>
```

### 3. Verify

```bash
lake build
```

The build must succeed with no errors and no `sorry` axioms.

### 4. Update the README

Add a row to the instruction table in `README.md`.

## Style Guidelines

- Follow the proof structure used in `Mulh.lean` as a template
- Include doc-strings (`/-! ... -/` and `/-- ... -/`) explaining the proof strategy
- Add concrete `#eval` sanity checks where practical
- Keep proofs modular: factor key lemmas out of the main theorem

## Checking for `sorry`

A proof is only considered complete when it contains no `sorry`. To check:

```bash
grep -r "sorry" JoltBytecode/
```

This should return no results for completed proofs.
