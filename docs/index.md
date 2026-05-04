# Jolt QED

Jolt QED is a Lean formalization effort for the Jolt bytecode expansion and
proof-system semantics.

This site is the public-facing project index. Detailed planning notes live in
`planning/` in the repository.

## Main Projects

- [Bytecode Expansion](projects/bytecode-expansion.md)
- [Lookup Table Verification](projects/lookup-table-verification.md)
- [Jolt ISA](projects/jolt-isa.md)

## Current Focus

The immediate focus is to make the bytecode expansion story complete and to
begin the lookup-table verification layer.

## Sumcheck Rendering Check

Inline math: \( g_1(r_1) = \sum_{b \in \{0,1\}} g(r_1, b) \).

Block math:

\[
\sum_{b_1,\ldots,b_n \in \{0,1\}}
  f(b_1,\ldots,b_n)
  =
  g_1(0) + g_1(1)
\]
