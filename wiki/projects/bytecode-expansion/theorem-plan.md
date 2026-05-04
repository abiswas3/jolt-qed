# Bytecode Expansion Theorem Plan

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

| Slice | Status | Notes |
|---|---|---|
| ALU families | In progress | Dummy row. |
| Shift families | In progress | Needs sequence-lowering theorem coverage. |
| Load families | Planning | Requires memory-envelope assumptions. |
| Store families | Not started | Known incomplete area. |
| Atomics | Not started | Required for completion claim. |

## Local Theorem Pattern

| Theorem kind | Purpose |
|---|---|
| Instruction theorem | One source instruction matches its Jolt bytecode expansion. |
| Lowering theorem | One inline sequence has a reusable semantic meaning. |
| Family theorem | A group of related instructions share one proof pattern. |
| Program theorem | Instruction-local facts compose across the trace/program. |
