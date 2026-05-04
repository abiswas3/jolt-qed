# Lookup Table Verification

## Summary

Lookup Table Verification is a Lean project for proving that verifier-facing
table polynomials represent the intended public lookup tables. The first dummy
target is the AND table.

The content here is placeholder text. The structure is what matters.

## Metadata

| Field | Value |
|---|---|
| Status | Planning |
| Target | 2026-09-30 |
| Owner | Ari / Quang |
| Reviewer | TBD |
| Code area | Proof system / tables |
| Planning notes | `planning/LOOKUP_TABLE_VERIFICATION_PLAN.md` |

## Pages

| Page | Purpose |
|---|---|
| [Timeline](timeline.md) | Milestones, deadlines, and target dates. |
| [Status](status.md) | Dated progress updates. |
| [Design](design.md) | Technical explanation of the table/MLE proof. |
| [Theorem Plan](theorem-plan.md) | Target theorem statements and proof decomposition. |
| [Risks](risks.md) | Assumptions, blockers, and decisions. |

## Success Criteria

| Item | Done when |
|---|---|
| AND table entry function | Lean definition matches the Rust `materialize_entry` behavior. |
| AND MLE evaluator | Lean definition matches the Rust `evaluate_mle` behavior. |
| Boolean hypercube theorem | The MLE evaluator agrees with table entries on Boolean addresses. |
| Full MLE theorem | The evaluator is proved to be the multilinear extension of the table. |
| Generalization plan | The proof pattern is clear enough to repeat for other tables. |
