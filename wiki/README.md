# Jolt QED Project Wiki

![Wiki](https://img.shields.io/badge/wiki-source_of_truth-0b57d0)
![Render](https://img.shields.io/badge/render-GitHub_Markdown-24292f)
![Math](https://img.shields.io/badge/math-GitHub_LaTeX-7b1fa2)

This directory is the source of truth for project documentation. Every page
should be readable directly in GitHub without requiring a generated site.

> [!IMPORTANT]
> Keep the Markdown in this directory readable on GitHub by itself. Any future
> rendered site should treat `wiki/` as input, not as generated output.

## Projects

### [Bytecode Expansion](projects/bytecode-expansion/README.md)

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)
![Owner](https://img.shields.io/badge/owner-abiswas3-lightgrey)

- Owner: [abiswas3](https://github.com/abiswas3)
- Target: 2026-08-31
- Summary: Prove that Rust tracer bytecode expansion matches the Lean semantics.
- Pages: [timeline](projects/bytecode-expansion/timeline.md), [status](projects/bytecode-expansion/status.md), [design](projects/bytecode-expansion/design.md), [theorem plan](projects/bytecode-expansion/theorem-plan.md), [risks](projects/bytecode-expansion/risks.md)

### [Lookup Table Verification](projects/lookup-table-verification/README.md)

![Status](https://img.shields.io/badge/status-planning-yellow)
![Target](https://img.shields.io/badge/target-2026--09--30-green)
![Owner](https://img.shields.io/badge/owner-abiswas3-lightgrey)

- Owner: [abiswas3](https://github.com/abiswas3)
- Target: 2026-09-30
- Summary: Prove that verifier table polynomials represent the intended public lookup tables.
- Pages: [timeline](projects/lookup-table-verification/timeline.md), [status](projects/lookup-table-verification/status.md), [design](projects/lookup-table-verification/design.md), [theorem plan](projects/lookup-table-verification/theorem-plan.md), [risks](projects/lookup-table-verification/risks.md)

## Current Priorities

1. Close the bytecode expansion theorem structure for inline instruction sequences.
2. State the bytecode memory-region assumptions for loads and stores precisely.
3. Start lookup-table verification with the AND table MLE theorem.

## Global Checklist

- [x] Plain Markdown source directory exists.
- [x] Project pages render directly on GitHub.
- [x] Timelines and status pages have a consistent shape.
- [x] Markdown tables have been removed from the wiki source.
- [ ] Replace dummy project data with current facts.
- [ ] Add issue and PR links once the tracking policy is settled.

## Conventions

- `README.md` is the overview page for each directory.
- `timeline.md` tracks milestones and deadlines.
- `status.md` tracks dated updates.
- `design.md` explains how the project works.
- `theorem-plan.md` records target Lean theorem shapes.
- `risks.md` tracks assumptions, blockers, and open decisions.
- Do not use Markdown tables for content that needs frequent editing.

> [!TIP]
> Prefer headings, bullet lists, task lists, fenced code blocks, LaTeX blocks,
> badges, and GitHub alert blocks. Avoid raw HTML and generator-specific syntax
> in `wiki/`.

## Status Labels

- ![Todo](https://img.shields.io/badge/status-todo-lightgrey) `todo`: no serious work has begun.
- ![Planning](https://img.shields.io/badge/status-planning-yellow) `planning`: scope and theorem shape are being decided.
- ![In progress](https://img.shields.io/badge/status-in_progress-blue) `in progress`: active implementation or proof work is happening.
- ![Blocked](https://img.shields.io/badge/status-blocked-red) `blocked`: progress needs a decision, dependency, or design fix.
- ![Review](https://img.shields.io/badge/status-review-purple) `review`: work exists and needs checking.
- ![Done](https://img.shields.io/badge/status-done-brightgreen) `done`: the current target is complete.
