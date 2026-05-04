# Lookup Table Verification Timeline

## Milestones

| Date | Milestone | Status | Notes |
|---|---|---|---|
| 2026-06-01 | State AND table in Lean | Planning | Define entry function and evaluator. |
| 2026-06-15 | Boolean hypercube theorem | Not started | Prove evaluator agrees with materialized entries on Boolean points. |
| 2026-07-01 | Full MLE theorem | Not started | Prove evaluator is the multilinear extension of the table. |
| 2026-07-31 | Template for more tables | Not started | Generalize the AND proof pattern. |
| 2026-09-30 | Project checkpoint | Not started | Dummy target for the first lookup-table verification block. |

## Deadline Notes

- The first real proof should be the AND table, not a vague generic lookup
  relation.
- The Rust table is public but not materialized at verifier time.
- The Lean statement should be precise about `materialize_entry` and
  `evaluate_mle`.
