# Jolt ISA

## Goal

Maintain the Lean semantic model of the primitive Jolt instruction rows used by
expanded bytecode.

## Scope

- virtual-register primitives;
- memory primitives;
- assertion and advice primitives;
- semantic lemmas used by bytecode expansion proofs;
- bridge lemmas used by lookup-table verification.

## Current Status

Status: evolving with bytecode expansion coverage.

## Next Steps

- Keep the semantic primitive list aligned with Rust tracer rows.
- Record which primitives are enforced by lookup tables.
- Link each primitive to its bytecode and lookup-table proof obligations.

