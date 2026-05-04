# Bytecode Expansion

## Goal

Prove that Rust tracer bytecode expansions implement the intended architectural
semantics.

## Scope

- compositional lowering theorems for recursively expanded instructions;
- loads and special memory regions;
- stores;
- atomics;
- `rd = x0` dispatch policy;
- advice tape connection;
- trace metadata, later;
- virtual-register renaming, later.

## Current Status

Status: in progress.

## Next Steps

- Fill in the current theorem coverage table.
- Identify the next missing instruction family.
- Link active issues and PRs.

