# Lookup Table Verification

![Status](https://img.shields.io/badge/status-planning-yellow)

- Owner: [abiswas3](https://github.com/abiswas3)
- Target: 2026-12-31

## Overview

In Jolt, verifying that the prover ran a logical or arithmetic instruction correctly reduces to a memory lookup. For a guest program written in 64-bit RISC-V assembly, Jolt exposes a public evaluation table of length $2^{128}$ for each supported instruction. The `AND` table, for example, has one row per $(x, y)$ pair, and the cell at that row holds the value of `x & y`.

Correctness then amounts to checking that the value written to the destination register `rd` matches the corresponding entry in the table. Of course we don't do this for every `AND` instruction in the guest program — instead, we batch them and run a single randomised check.

Glossing over the details, that randomised check reduces to evaluating the *multilinear extension* (MLE) of the `AND` table — and of the table for each other supported instruction — at a random point. The technical innovation is that although the table is enormous, the verifier never materialises it: the MLE can be evaluated efficiently from a closed-form expression.

## What we're proving

The formal verification task is to show that the efficient MLE-evaluation algorithm Jolt uses really does compute the multilinear extension of the underlying instruction table — i.e. that the closed-form polynomial agrees with the table on every Boolean point, and is the unique multilinear polynomial that does so.

See [Design](design.md) for the concrete `AND`-table statement and the Lean shape of the two theorems we're chasing.

## Pages

- [Timeline](timeline.md): milestones, deadlines, and target dates.
- [Design](design.md): table definitions, MLE statement, Lean theorem sketch.
- [Risks](risks.md): assumptions, blockers, and decisions.


