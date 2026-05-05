# Lookup Table Verification

![Status](https://img.shields.io/badge/status-planning-yellow)
![Target](https://img.shields.io/badge/target-2026--09--30-green)
![Owner](https://img.shields.io/badge/owner-abiswas3-lightgrey)
![Area](https://img.shields.io/badge/area-lookup_tables-24292f)

## Summary

Lookup Table Verification is a Lean project for proving that verifier-facing
table polynomials represent the intended public lookup tables. The first dummy
target is the AND table.

> [!NOTE]
> The content here is placeholder text. The structure is what matters.

## Metadata

- Status: ![Planning](https://img.shields.io/badge/status-planning-yellow)
- Target: 2026-09-30
- Owner: [abiswas3](https://github.com/abiswas3)
- Reviewer: TBD
- Code area: proof system / tables
- Planning notes: `planning/LOOKUP_TABLE_VERIFICATION_PLAN.md`

## Pages

- [Timeline](timeline.md): milestones, deadlines, and target dates.
- [Status](status.md): dated progress updates.
- [Design](design.md): technical explanation of the table/MLE proof.
- [Theorem Plan](theorem-plan.md): target theorem statements and proof decomposition.
- [Risks](risks.md): assumptions, blockers, and decisions.

## Success Criteria

- [ ] Lean definition matches the Rust `materialize_entry` behavior for AND.
- [ ] Lean definition matches the Rust `evaluate_mle` behavior for AND.
- [ ] The MLE evaluator agrees with table entries on Boolean addresses.
- [ ] The evaluator is proved to be the multilinear extension of the table.
- [ ] The proof pattern is clear enough to repeat for other tables.

## Project Checklist

- [x] Project page skeleton exists.
- [x] Timeline, status, design, theorem plan, and risks pages exist.
- [ ] Replace dummy target dates with the real schedule.
- [ ] Add concrete Lean names for the AND table definitions.
- [ ] Link the relevant Rust table implementation.
