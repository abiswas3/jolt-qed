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



## Global Checklist


## Status Labels

- ![Todo](https://img.shields.io/badge/status-todo-lightgrey) `todo`: no serious work has begun.
- ![Planning](https://img.shields.io/badge/status-planning-yellow) `planning`: scope and theorem shape are being decided.
- ![In progress](https://img.shields.io/badge/status-in_progress-blue) `in progress`: active implementation or proof work is happening.
- ![Blocked](https://img.shields.io/badge/status-blocked-red) `blocked`: progress needs a decision, dependency, or design fix.
- ![Review](https://img.shields.io/badge/status-review-purple) `review`: work exists and needs checking.
- ![Done](https://img.shields.io/badge/status-done-brightgreen) `done`: the current target is complete.
