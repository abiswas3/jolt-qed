---
name: proving
description: Lean/mathlib proof guidance for advising on theorem proving, proof cleanup, tactic choice, simp/rw usage, theorem/API design, and maintainable Lean proofs. Use when Codex is asked to explain or improve Lean proofs, especially when the user wants mathlib-style advice rather than direct edits.
---

# Proving

## Operating Mode

Respect the user's requested mode. If the user asks for advice only, inspect and explain but do
not edit files. If edits are requested, keep them scoped to the named proof or nearby helper API.

When advising, first read the theorem, nearby lemmas, imports, and call sites. Prefer guidance
grounded in the actual goal shape and local APIs over generic Lean advice.

## Mathlib Proof Style

- Prefer small API lemmas over repeated proof plumbing.
- Prefer theorem statements in normal form, with assumptions and conclusions matching how the
  result will be used.
- Use `rw` for deliberate, named transformations.
- Use `simp` to normalize expressions, discharge routine goals, or finish via `simpa`.
- Use `simp only [...]` for non-terminal simplification when later steps depend on the resulting
  goal shape.
- Terminal `simp` is acceptable. Do not blindly replace a short terminal `simp` with a long
  `simp only` list unless performance, fragility, or review pressure requires it.
- Avoid non-terminal plain `simp` followed by rigid tactics such as `rw`, unless the output is not
  part of a fragile proof path.
- Prefer `simpa [lemmas] using h` over `simp [lemmas] at h; exact h` when it cleanly closes.
- Use `simp_rw [lemmas]` when repeated rewriting under binders is intended.
- Use `calc` for readable equality chains and `change` when exposing the intended target shape.
- Treat `erw` or extra `rfl` after `simp`/`rw` as a sign that an API lemma may be missing.

## Simp Lemma Discipline

Mark a lemma `@[simp]` only when its right side is the intended normal form. Simp rewrites
directionally, so avoid lemmas that expand terms, loop, or encode a non-canonical preference.

For local proof scripts, prefer explicit lists:

```lean
simp only [h1, h2, some_def]
```

Use `simp?` interactively to discover needed lemmas, then decide whether the generated list is
worth keeping.

## Project Pattern Notes

For Jolt/Sail equivalence proofs, separate semantic content from plumbing:

- concrete execution lemmas should establish the final `SailJoltState`;
- factoring lemmas should expose the Sail monadic shape;
- final equivalence closers should mostly destruct witnesses, rewrite named equalities, and
  normalize the monadic computation;
- if the same `wX_shape` / `stateAfterWrite` bridge appears repeatedly, consider a helper lemma.

For ALUFamily proof cleanup, treat
`JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Mulw.lean`
as the current gold-standard proof shape. When closing the remaining ALUFamily files one by one,
preserve that structure unless the instruction genuinely needs extra facts:

- obtain source-register values once from `WellFormed`;
- place each local value definition immediately before the instruction block that uses it;
- each instruction block should say: what it reads, what value/state it writes, and that it
  succeeds;
- instruction helper outputs should be named by role, for example `h_mul_reads_rs1`,
  `h_mul_writes_product`, and `h_mul_succeeds`, rather than opaque names like `hrun`,
  `hw`, or `s_raw`;
- program success should be an explicit straight-line chain of
  `JoltISA.execProgram_instr_run_retire` rewrites;
- after the instruction trace, name the final Jolt value/state fact separately;
- name the pure value bridge separately, prove it with `simp only [...]` plus `exact` when the
  user is asking for explicit proof scripts, and make the comment about values, not state;
- once the value bridge is established, the remaining final-state proof should be mechanical;
- the top-level equivalence theorem may be proved directly from the concrete theorem and Sail
  factoring theorem when that reads better than calling a generic closer.

For Jolt ISA instruction-equivalence proofs, treat each Jolt program as the
sequence of Jolt instructions described by the expansion semantics:

- instruction semantics belong with the instruction, under
  `JoltISA/Semantics/Instructions/<Instruction>.lean`;
- each instruction should have run lemmas that state its source reads, state or
  virtual-register update, and return status;
- for real-register writes, prefer helpers that return a checkpoint `SailJoltState`, explicit
  source-read facts, a `stateAfterWrite` fact for the written value, and the `execInstr` success
  equation. Avoid vague names such as `_of_read` or `_of_reads`; name helpers and hypotheses by
  the instruction and semantic role;
- concrete program proofs should read as: instruction 1 lemma, instruction 2
  lemma, ..., named math bridge, final state-write collapse;
- each instruction-equivalence file should have a module-level comment listing
  the Jolt program sequence for the reader;
- in concrete program proofs, place a short comment before each emitted
  instruction block naming the instruction and the value/state update it proves;
- mark the core arithmetic/bitvector bridge with `-- NOTE: Math theorem: ...`
  where the concrete proof hands off from instruction semantics to math;
- do not hide the instruction sequence behind a custom tactic until the
  instruction-local API has stabilized and repeated proof shape is obvious;
- avoid non-terminal plain `simp` in production proofs. Use named rewrites,
  `simpa [...] using h`, or `simp only [...]` when the resulting shape matters.
- do not use large `maxHeartbeats` overrides to force slow proofs through;
  if a proof needs one, split out API lemmas or simplify the proof shape.

## Sources

Use [references/sources.md](references/sources.md) when source attribution is requested or when
checking whether guidance still matches current Lean/mathlib docs.
