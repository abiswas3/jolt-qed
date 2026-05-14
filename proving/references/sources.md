# Sources

Last consulted: 2026-05-14.

Primary references:

- Lean Reference, The Simplifier:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/
- Lean Reference, Invoking the Simplifier:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/
- Lean Reference, Rewrite Rules:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/
- Lean Reference, Simp Sets:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/
- Lean Reference, Terminal vs Non-Terminal Positions:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/Terminal-vs-Non-Terminal-Positions/
- Lean Reference, Simplification vs Rewriting:
  https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/
- Mathlib Library Style Guidelines:
  https://leanprover-community.github.io/contribute/style.html
- Mathlib flexible linter docs:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter/FlexibleLinter.html
- Mathlib `simp_rw` docs:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/SimpRw.html

Guidance extracted from these sources:

- `simp` is for simplifying to normal forms with a simp set.
- `simp only [...]` starts from an empty simp set, making intermediate simplification more stable.
- `rw` is for hand-selected rewrites and more precise proof steps.
- Mathlib discourages non-terminal plain `simp` when later rigid tactics depend on its output.
- Mathlib does not recommend squeezing every terminal `simp`; short terminal `simp` calls are
  usually more maintainable than long generated `simp only` lists.
- Simp lemmas should rewrite toward simpler or canonical right-hand sides.
