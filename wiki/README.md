# Jolt QED Project Wiki


This project is an attempt to formalise the [Jolt Zk-VM]() in Lean4.

> [!IMPORTANT]
> This project is currently under active development. 
> We will aim to keep the wiki as up to date as possible, but the code and roadmap map are subject to change,


## Active Projects

### [Bytecode Expansion](projects/bytecode-expansion/README.md)

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Owner: [abiswas3](https://github.com/abiswas3)
- Expected Completion date: 2026-08-31
- Summary: The Lean build passes and many main bytecode-expansion theorems are now in place, including shifts, word instructions, loads, and the advice division/remainder family. Stores, atomics, and a few bridge lemmas remain open. See [progress report](projects/bytecode-expansion/timeline.md) and [risks](projects/bytecode-expansion/risks.md).

- Pages: 
    - [progress report](projects/bytecode-expansion/timeline.md)
    - [project wiki](projects/bytecode-expansion/design.md)
    - [risks](projects/bytecode-expansion/risks.md)

### [Lookup Table Verification](projects/lookup-table-verification/README.md)

![Status](https://img.shields.io/badge/status-planning-yellow)

- Owner: [abiswas3](https://github.com/abiswas3)
- Target: 2026-12-31
- Summary: Prove the each lookup table is correctly evaluated at a random point.

- Pages: 
    - [progress report](projects/lookjup-table-verification/timeline.md)
    - [project wiki](projects/lookjup-table-verification/design.md)
    - [risks](projects/lookjup-table-verification/risks.md)


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
