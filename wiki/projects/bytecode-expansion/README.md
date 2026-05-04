# Bytecode Expansion

## Summary

Bytecode Expansion is a Lean verification project for the Rust tracer expansion
pipeline. The goal is to prove that each Jolt bytecode expansion implements the
intended instruction semantics under explicit assumptions.

The content on this page is dummy data. It exists to test whether the raw
Markdown layout is clean enough to read directly on GitHub.

## Metadata

| Field | Value |
|---|---|
| Status | In progress |
| Target | 2026-08-31 |
| Owner | Ari |
| Reviewer | TBD |
| Code area | `JoltBytecode/` |
| Planning notes | `planning/JOLT_COMPOSITIONAL_LOWERING_PLAN.md` |

## Pages

| Page | Purpose |
|---|---|
| [Timeline](timeline.md) | Milestones, deadlines, and target dates. |
| [Status](status.md) | Dated progress updates. |
| [Design](design.md) | Technical explanation of how the project works. |
| [Theorem Plan](theorem-plan.md) | Target theorem statements and proof decomposition. |
| [Risks](risks.md) | Assumptions, blockers, and decisions. |

## Success Criteria

| Item | Done when |
|---|---|
| Instruction coverage | Every Rust tracer bytecode expansion has a Lean theorem or an explicit exclusion. |
| Compositional lowering | Instructions that expand into sequences use semantic lowering theorems instead of duplicated nested proofs. |
| Memory envelope | Load/store theorems state ordinary-RAM and special-region assumptions precisely. |
| Atomics | Missing atomic expansions have statements and proof skeletons. |
| Audit cleanup | Known limitations are either fixed or explicitly documented as theorem assumptions. |

## Current Snapshot

| Area | Status | Note |
|---|---|---|
| ALU word instructions | In progress | Dummy row. |
| Shifts | In progress | Dummy row. |
| Loads | Planning | Needs precise memory envelope. |
| Stores | Not started | Known incomplete area. |
| Atomics | Not started | Required before August completion target. |
