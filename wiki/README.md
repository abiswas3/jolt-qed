# Jolt QED Project Wiki

This directory is the source of truth for project documentation. Every page
should be readable directly in GitHub without requiring a generated site.

## Projects

| Project | Status | Target | Owner | Summary |
|---|---|---:|---|---|
| [Bytecode Expansion](projects/bytecode-expansion/README.md) | In progress | 2026-08-31 | Ari | Prove that Rust tracer bytecode expansion matches the Lean semantics. |
| [Lookup Table Verification](projects/lookup-table-verification/README.md) | Planning | 2026-09-30 | Ari / Quang | Prove that verifier table polynomials represent the intended public lookup tables. |

## Current Priorities

| Priority | Project | Note |
|---|---|---|
| 1 | Bytecode Expansion | Close the theorem structure for inline instruction sequences. |
| 2 | Bytecode Expansion | State the memory-region assumptions for loads and stores precisely. |
| 3 | Lookup Table Verification | Start with the AND table MLE theorem. |

## Conventions

- `README.md` is the overview page for each directory.
- `timeline.md` tracks milestones and deadlines.
- `status.md` tracks dated updates.
- `design.md` explains how the project works.
- `theorem-plan.md` records target Lean theorem shapes.
- `risks.md` tracks assumptions, blockers, and open decisions.

## Status Labels

| Label | Meaning |
|---|---|
| Not started | No serious work has begun. |
| Planning | Scope and theorem shape are being decided. |
| In progress | Active implementation or proof work is happening. |
| Blocked | Progress needs a decision, dependency, or design fix. |
| Review | Work exists and needs checking. |
| Done | The current target is complete. |
