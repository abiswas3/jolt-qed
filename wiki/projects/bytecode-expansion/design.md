# Bytecode Expansion Design

## Problem

The Rust tracer expands some source-level instructions into Jolt bytecode
sequences. The Lean development should prove that these expansions preserve the
intended semantics without expanding every nested sequence from scratch at every
use site.

## Intended Approach

Use compositional lowering theorems. If an instruction lowers into a sequence,
prove the semantic theorem once. Any caller that contains that sequence can use
the theorem by transitivity.

## Dummy Theorem Shape

```lean
theorem slli_lowering_correct
    (s : JoltSailState)
    (h : BytecodeExpansionAssumptions s) :
    runJoltSequence (lowerSlli inst) s =
      runRiscvInstruction inst s := by
  sorry
```

Then callers use the existing theorem:

```lean
theorem caller_correct
    (s : JoltSailState)
    (h : BytecodeExpansionAssumptions s) :
    runJoltSequence (lowerCaller inst) s =
      runRiscvInstruction inst s := by
  -- use slli_lowering_correct for the nested lowering step
  sorry
```

## Memory Envelope

The load/store theorems should explicitly state the memory subset they cover.
For example, a load theorem may require that the computed address lies in
ordinary RAM rather than a special Jolt region.

Dummy statement:

$$
\text{ordinaryRAM}(a) \land \text{aligned}(a, w)
\Rightarrow
\text{loadTheorem}(a, w)
$$

## Open Design Questions

| Question | Current answer |
|---|---|
| Do inline sequences get expanded at every caller? | No. Use lowering theorems. |
| Are special memory regions modeled? | Not yet. Track as explicit assumptions. |
| Is virtual-register renaming part of the first pass? | No. Track separately unless it blocks theorem statements. |
