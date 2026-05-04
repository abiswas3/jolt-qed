# Bytecode Expansion Timeline

## Milestones

| Date | Milestone | Status | Notes |
|---|---|---|---|
| 2026-06-15 | Baseline Jolt ISA in Lean | In progress | Dummy checkpoint for stable instruction definitions. |
| 2026-06-30 | Lowering theorem framework | Planning | Define the reusable theorem pattern for inline sequences. |
| 2026-07-15 | Load/store theorem envelope | Planning | State ordinary-RAM and special-region assumptions. |
| 2026-07-31 | Missing instruction families | Planning | Fill gaps for advice, stores, and boundary variants. |
| 2026-08-15 | Atomics pass | Not started | Add AMO, LR, and SC theorem skeletons. |
| 2026-08-31 | Final audit pass | Not started | Close or document trace metadata and virtual-register issues. |

## Deadline Notes

- The August target assumes the current Jolt ISA work remains stable.
- Store modeling and atomics are the main dummy blockers.
- Trace metadata and virtual-register renaming are tracked separately unless
  they become theorem blockers.
