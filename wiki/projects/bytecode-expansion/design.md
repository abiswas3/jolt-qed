# Bytecode Expansion Design

![Type](https://img.shields.io/badge/type-design_note-24292f)
![Project](https://img.shields.io/badge/project-bytecode_expansion-blue)

## Problem

The Rust tracer expands some source-level instructions into Jolt bytecode
sequences. The Lean development should prove that these expansions preserve the
intended semantics without expanding every nested sequence from scratch at every
use site.

> [!TIP]
> The design rule is compositionality: prove each lowering theorem once, then
> reuse it in caller proofs.

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

### Do inline sequences get expanded at every caller?

- Current answer: no. Use lowering theorems.

### Are special memory regions modeled?

- Current answer: not yet. Track as explicit assumptions.

### Is virtual-register renaming part of the first pass?

- Current answer: no. Track separately unless it blocks theorem statements.

## Design Checklist

- [x] Use compositional lowering as the default proof shape.
- [ ] State the memory-region envelope in the theorem assumptions.
- [ ] Decide how trace metadata enters the final theorem.
- [ ] Decide whether virtual-register renaming is a theorem or a convention.
