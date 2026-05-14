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

## Sources

Use [references/sources.md](references/sources.md) when source attribution is requested or when
checking whether guidance still matches current Lean/mathlib docs.
