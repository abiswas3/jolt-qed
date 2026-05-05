# Bytecode Expansion Timeline

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)

> [!IMPORTANT]
> Dates below are dummy planning dates. Replace them with the real project
> commitments before sharing this as the authoritative schedule.

## Milestones

### 2026-06-15: Baseline Jolt ISA in Lean

![Status](https://img.shields.io/badge/status-in_progress-blue)

- Notes: dummy checkpoint for stable instruction definitions.

### 2026-06-30: Lowering Theorem Framework

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: define the reusable theorem pattern for inline sequences.

### 2026-07-15: Load/Store Theorem Envelope

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: state ordinary-RAM and special-region assumptions.

### 2026-07-31: Missing Instruction Families

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: fill gaps for advice, stores, and boundary variants.

### 2026-08-15: Atomics Pass

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: add AMO, LR, and SC theorem skeletons.

### 2026-08-31: Final Audit Pass

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: close or document trace metadata and virtual-register issues.

## Deadline Notes

- The August target assumes the current Jolt ISA work remains stable.
- Store modeling and atomics are the main dummy blockers.
- Trace metadata and virtual-register renaming are tracked separately unless
  they become theorem blockers.

## Immediate Timeline Tasks

- [ ] Replace dummy dates with real commitments.
- [ ] Add issue links for store and atomic milestones.
- [ ] Mark which milestones block the paper story.
