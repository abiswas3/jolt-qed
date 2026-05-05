# Bytecode Expansion

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)
![Owner](https://img.shields.io/badge/owner-abiswas3-lightgrey)
![Area](https://img.shields.io/badge/area-JoltBytecode-24292f)

## Summary

Bytecode Expansion is a Lean verification project for the Rust tracer expansion
pipeline. The goal is to prove that each Jolt bytecode expansion implements the
intended instruction semantics under explicit assumptions.

> [!NOTE]
> This page still uses dummy data. The layout is intended to test whether native
> GitHub Markdown is good enough for the project wiki.

## Metadata

- Status: ![In progress](https://img.shields.io/badge/status-in_progress-blue)
- Target: 2026-08-31
- Owner: [abiswas3](https://github.com/abiswas3)
- Reviewer: TBD
- Code area: `JoltBytecode/`
- Planning notes: `planning/JOLT_COMPOSITIONAL_LOWERING_PLAN.md`

## Pages

- [Timeline](timeline.md): milestones, deadlines, and target dates.
- [Status](status.md): dated progress updates.
- [Design](design.md): technical explanation of how the project works.
- [Theorem Plan](theorem-plan.md): target theorem statements and proof decomposition.
- [Risks](risks.md): assumptions, blockers, and decisions.

## Success Criteria

- [ ] Every Rust tracer bytecode expansion has a Lean theorem or an explicit exclusion.
- [ ] Instructions that expand into sequences use semantic lowering theorems instead of duplicated nested proofs.
- [ ] Load/store theorems state ordinary-RAM and special-region assumptions precisely.
- [ ] Missing atomic expansions have statements and proof skeletons.
- [ ] Known limitations are either fixed or explicitly documented as theorem assumptions.

## Project Checklist

- [x] Project page skeleton exists.
- [x] Timeline, status, design, theorem plan, and risks pages exist.
- [ ] Replace dummy instruction coverage with current Lean status.
- [ ] Link relevant issues and PRs.
- [ ] Decide whether August target needs per-family owners.

## Current Snapshot

### ALU Word Instructions

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Note: dummy row.

### Shifts

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Note: dummy row.

### Loads

![Status](https://img.shields.io/badge/status-planning-yellow)

- Note: needs precise memory envelope.

### Stores

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Note: known incomplete area.

### Atomics

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Note: required before August completion target.
