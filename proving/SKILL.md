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

## ALUFamily Proof Standard

As of 2026-05-15, the cleaned `ALUFamily` proofs use
`JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Mulw.lean` as the
gold-standard shape. Preserve that structure unless the instruction genuinely
needs extra arithmetic facts.

Current layout:

- the old `EmbeddedSailJoltState` directory has been flattened into
  `JoltBytecode`;
- `ALUFamily/Rtype/W`, `ALUFamily/Rtype/Shift`, `ALUFamily/Itype/W`, and
  `ALUFamily/Itype/Shift` have been flattened into `ALUFamily/Rtype` and
  `ALUFamily/Itype`;
- do not recreate `ALUFamily/*/Family.lean`;
- do not recreate `ALUFamily/Bridges`; bridge lemmas live in the instruction
  file that uses them.

Each instruction file should read in this order:

1. imports for the local instruction semantics and expansion definitions;
2. `abbrev <instr>_sail_operation ...` for the Sail value;
3. `abbrev <instr>_jolt_val ...` for the final Jolt value, when the expansion
   has a nontrivial value chain;
4. local arithmetic/bitvector bridge lemmas, ending in a named value theorem;
5. Sail factoring theorem, if the top-level equivalence uses one;
6. concrete program theorem;
7. top-level `...Program_eq_sail` theorem.

Concrete theorem shape:

- obtain source-register values once from `WellFormed`;
- place each local value definition immediately before the instruction block
  that uses it;
- each instruction block states exactly what the instruction reads, what value
  or state it writes, and that it succeeds;
- instruction helper outputs must be named by semantic role, for example
  `js_afterMul`, `h_mul_reads_rs1`, `h_mul_writes_product`,
  `h_mul_succeeds`; avoid opaque names like `hrun`, `hw`, `s_raw`,
  `hread_add`, or `_of_read`;
- do not put nested local `by` blocks inside instruction plumbing if a helper
  lemma can expose the read/write/success facts directly;
- if proof plumbing starts to grow, move it into an instruction-local helper
  under `JoltISA/Semantics/Instructions/<Instruction>.lean`, not into the
  concrete theorem.

Program success:

- keep the emitted instruction sequence visible;
- prove program success with an explicit straight-line chain of
  `JoltISA.execProgram_instr_run_retire` rewrites;
- do not hide two-instruction programs and longer programs behind different
  patterns; they should both look like the same straight-line proof shape.

Value/state close:

- after the instruction trace, name the fact that the final checkpoint contains
  the final Jolt value, for example `h_final_jolt_value`;
- name the pure value bridge separately, for example `h_mulw_value`;
- comments must describe values, not state, around the value bridge;
- when explicit proof style is requested, prove definitional cleanup by
  `simp only [...]` followed by `exact ...`, rather than plain `simpa`;
- after the value bridge, the final-state proof should be mechanical: rewrite
  the goal to the Jolt value and exact the named final-state fact;
- use `calc` only when it improves readability. For same-register repeated
  writes, prefer a helper such as `stateAfterWrite_stateAfterWrite` plus one
  final value rewrite over a long equality chain.

Naming/API constraints:

- prefer `sail_operation`/`<instr>_sail_operation` and
  `jolt_val`/`<instr>_jolt_val` for meaningful values;
- do not add wrapper definitions that merely rename a single existing function
  without improving the proof narrative;
- instruction semantics lemmas should be named by what instruction/state they
  produce, e.g. `exists_state_after_mul_run_xreg_xreg_xreg`, not by vague
  phrases like `_of_reads`;
- theorem statements for instruction helpers should return the checkpoint
  `SailJoltState`, source-read facts when useful, the write/update fact, and
  the `execInstr` success equation.

Top-level equivalence:

- it is acceptable to prove the top-level theorem directly from the concrete
  theorem and Sail factoring theorem when that is clearer than a generic
  closer;
- avoid generic closers if they obscure the human story: "instruction 1 writes
  `f(v1, v2)`, instruction 2 writes `g(f(v1, v2))`, and the math theorem proves
  that final Jolt value equals Sail's value."

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
