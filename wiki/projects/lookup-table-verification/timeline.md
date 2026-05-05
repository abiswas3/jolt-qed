# Lookup Table Verification Timeline

![Status](https://img.shields.io/badge/status-planning-yellow)
![Target](https://img.shields.io/badge/target-2026--09--30-green)

> [!IMPORTANT]
> The first milestone should stay concrete: prove the AND table evaluator,
> then generalize. Do not start with vague "lookup relation" wording.

## Milestones

### 2026-06-01: State AND Table in Lean

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: define entry function and evaluator.

### 2026-06-15: Boolean Hypercube Theorem

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: prove evaluator agrees with materialized entries on Boolean points.

### 2026-07-01: Full MLE Theorem

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: prove evaluator is the multilinear extension of the table.

### 2026-07-31: Template for More Tables

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: generalize the AND proof pattern.

### 2026-09-30: Project Checkpoint

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: dummy target for the first lookup-table verification block.

## Deadline Notes

- The first real proof should be the AND table, not a vague generic lookup
  relation.
- The Rust table is public but not materialized at verifier time.
- The Lean statement should be precise about `materialize_entry` and
  `evaluate_mle`.

## Immediate Timeline Tasks

- [ ] Replace dummy dates with the real plan.
- [ ] Add issue links for AND Boolean-hypercube agreement.
- [ ] Add issue links for full MLE correctness.
