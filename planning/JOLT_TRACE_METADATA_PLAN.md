# Plan: Trace Metadata

This note records a known issue that we are intentionally not solving now.

## Issue

The Lean instruction-equivalence theorems mostly prove semantic behavior:

```text
projectResult (Jolt expansion run) = Sail architectural execution
```

They generally do not prove exact trace-row metadata agreement with Rust.

Rust annotates final expanded rows with metadata such as:

- `virtual_sequence_remaining`
- `is_first_in_sequence`
- `is_compressed`
- instruction address / PC metadata

This metadata is filled in by Rust's `InstrAssembler::finalize` after the final
sequence length is known. It is important for exact trace format and prover
inputs, but it is not part of the architectural state equality proved by the
current Lean theorems.

## Current Position

This is not a blocker for semantic instruction equivalence.

The current Lean claim should be read as:

```text
the expanded instruction sequence has the same architectural effect as Sail
```

not:

```text
the Lean model reproduces every trace row and every trace metadata field exactly
```

## Later Work

When we want exact trace-row faithfulness, add a separate trace-format layer:

```text
source instruction
  -> recursively expanded rows
  -> finalized rows with metadata
```

Potential theorem shape:

```text
finalize(expand(instr)) assigns virtual_sequence_remaining,
is_first_in_sequence, compression, and address metadata exactly as Rust does.
```

This should be handled after the semantic lowering and memory-region work.

