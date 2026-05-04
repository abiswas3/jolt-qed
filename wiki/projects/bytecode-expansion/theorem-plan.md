# Bytecode Expansion Theorem Plan

![Type](https://img.shields.io/badge/type-theorem_plan-24292f)
![Status](https://img.shields.io/badge/status-in_progress-blue)

## Main Target

The eventual theorem should relate a lowered Jolt program to the intended
instruction semantics under explicit assumptions.

```lean
theorem bytecode_expansion_correct
    (prog : RiscvProgram)
    (s : JoltSailState)
    (h : BytecodeExpansionAssumptions s) :
    runJoltProgram (lowerProgram prog) s =
      runRiscvProgram prog s := by
  sorry
```

This is dummy notation. The final statement should use the actual Lean names.

## Proof Slices

### ALU Families

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Notes: dummy row.

### Shift Families

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Notes: needs sequence-lowering theorem coverage.

### Load Families

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: requires memory-envelope assumptions.

### Store Families

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: known incomplete area.

### Atomics

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: required for completion claim.

## Local Theorem Pattern

### Instruction Theorem

- Purpose: one source instruction matches its Jolt bytecode expansion.

### Lowering Theorem

- Purpose: one inline sequence has a reusable semantic meaning.

### Family Theorem

- Purpose: a group of related instructions share one proof pattern.

### Program Theorem

- Purpose: instruction-local facts compose across the trace/program.

> [!WARNING]
> Do not let the final theorem silently claim full Rust CPU/MMU behavior unless
> the memory and trace assumptions have actually been modeled.
