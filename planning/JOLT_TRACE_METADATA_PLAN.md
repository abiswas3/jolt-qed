# Plan: Trace Metadata

Status: open, non-blocking for semantic bytecode equivalence.

This note records a known issue that is intentionally outside the current
semantic instruction-equivalence theorem layer.

## Current Claim

The current Lean theorems prove architectural behavior:

```text
projectResult (Jolt expansion run) = Sail architectural execution
```

They should not be read as exact trace-row-format theorems.

## Metadata Not Yet Proved

Rust annotates final expanded rows with metadata such as:

- `virtual_sequence_remaining`;
- `is_first_in_sequence`;
- `is_compressed`;
- instruction address / PC metadata.

This metadata is filled in by Rust's finalization path after the final expanded
sequence length is known. It matters for exact trace format and prover inputs,
but it is not part of the architectural state equality proved by the current
Lean theorems.

## Risk Classification

This is not a blocker for semantic instruction equivalence.

It is a separate trace-format faithfulness claim:

```text
source instruction
  -> recursively expanded rows
  -> finalized rows with metadata
```

The current Lean claim is only:

```text
expanded instruction sequence has the same architectural effect as Sail
```

not:

```text
Lean reproduces every Rust trace row and every metadata field exactly
```

## Later Work

When exact trace-row faithfulness is in scope, add a separate finalization model
and prove a theorem of the form:

```text
finalize(expand(instr)) assigns virtual_sequence_remaining,
is_first_in_sequence, compression, and address metadata exactly as Rust does.
```

This should be handled after the semantic theorem envelope is explicit and after
the Rust-side expansion provenance story is settled.
