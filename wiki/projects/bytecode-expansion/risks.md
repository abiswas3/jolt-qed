# Bytecode Expansion Risks


## AI Generated Audit

The following were flagged as **Risks** in an AI generated audit.

### Recursive Expansion Is Not Yet Final-Row Faithful

![Risk](https://img.shields.io/badge/risk-recursive_expansion-red)

- Issue: many Lean definitions model the source-level `emit_*` sequence, while
  Rust recursively lowers each emitted instruction through `inst.inline_sequence`.
- Impact: a theorem can prove the source expansion correct without proving that
  the final Rust bytecode rows have the same semantics.
- Response: prove compositional lowering theorems for the recursively lowered
  pieces, then use them in caller proofs.

### Missing Virtual And Boundary Lowering Variants

![Risk](https://img.shields.io/badge/risk-lowering_variants-red)

- Issue: architectural real-register theorems do not always match how callers use
  lowered instructions with virtual registers or real/virtual boundaries.
- Impact: loads, stores, advice sequences, and shift-heavy expansions cannot be
  connected cleanly to final primitive rows.
- Response: add variants for `SLLI`, `SLL`, `SRLI`, `SRL`, `SRAI`, `SRA`, and
  the word variants where caller expansions need them.

### Rust-To-Lean Expansion Drift Is Manual

![Risk](https://img.shields.io/badge/risk-expansion_manifest-yellow)

- Issue: the correspondence between Rust inline expansion and Lean definitions is
  currently checked manually.
- Impact: Rust changes can invalidate Lean definitions without an immediate
  signal.
- Response: generate a manifest containing the source inline sequence, final
  recursively expanded rows, metadata, and allocated virtual registers.

### Virtual-Register Allocation Is Only Informal

![Risk](https://img.shields.io/badge/risk-vreg_renaming-yellow)

- Issue: Lean often uses fixed virtual-register names, while Rust uses an
  allocator whose output depends on allocator state, reserved registers, inline
  temporaries, and nested expansion.
- Impact: the proof currently relies on the informal assumption that the fixed
  Lean names are fresh and disjoint in the same way Rust's allocated names are.
- Response: prove a virtual-register renaming theorem, or parameterize expansions
  over allocator outputs.

### `rd = x0` Policy Is Outside Many Theorems

![Risk](https://img.shields.io/badge/risk-rd_x0-yellow)

- Issue: many Lean theorems assume `rd != x0`, while Rust has explicit handling
  for `rd = x0`.
- Impact: no-op replacement and side-effecting remaps are not covered by those
  theorem statements.
- Response: classify the Rust behavior by instruction class and add wrapper
  theorems for the dispatch policy.

### Trace Failure And Architectural Traps Are Mixed

![Risk](https://img.shields.io/badge/risk-traps_vs_failures-yellow)

- Issue: some Lean load proofs model misalignment as a Sail memory exception,
  while Rust inline sequences often use virtual assertions that panic or fail the
  trace.
- Impact: the theorem boundary can look stronger than it is.
- Response: either model accept/reject behavior explicitly or strengthen
  preconditions to the flat, aligned, non-trapping subset.

### Memory Envelope Is Not Centralized

![Risk](https://img.shields.io/badge/risk-memory_envelope-red)

- Issue: Lean assumes flat, populated, machine-mode memory, while Rust has MMU,
  device, advice, host, panic, output, termination, and zero-padding regions.
- Impact: load/store theorems may overclaim unless ordinary-RAM assumptions are
  explicit.
- Response: introduce a single `JoltFlatMemoryEnvelope` or equivalent predicate
  and use it consistently in load/store theorem statements.

### Special Memory Regions Need A Separate Device Layer

![Risk](https://img.shields.io/badge/risk-device_regions-yellow)

- Issue: Sail treats memory as a hash map of bytes, while Rust/Jolt interprets
  some numeric address ranges as device state.
- Impact: input, advice, output, panic, termination, and zero-padding behavior are
  not plain Sail-memory equivalence.
- Response: keep the short-term theorem envelope to ordinary RAM, then add a
  Jolt device-state model for special regions.

### Advice Tape Behavior Is Not Modeled

![Risk](https://img.shields.io/badge/risk-advice_tape-yellow)

- Issue: Lean models advice as explicit values, while Rust `VirtualAdviceLoad`
  reads little-endian bytes from a mutable FIFO tape and can fail on underflow.
- Impact: tape ordering, byte packing, depletion, and width canonicality are
  outside the current model.
- Response: add advice bytes and an advice cursor to the modeled execution state,
  then recover the existing explicit-advice theorems as a special case.

### Store Proofs Are Still Behind Loads

![Risk](https://img.shields.io/badge/risk-stores-red)

- Issue: `SB`, `SH`, and parts of `SW` remain incomplete.
- Impact: stores block a full bytecode-expansion theorem and interact directly
  with the memory-envelope risk.
- Response: start with `SW`, prove the read-modify-write splice lemma once, then
  instantiate it for `SW`, `SH`, and `SB`.

### Word-Shift Bridge Lemmas Still Have Holes

![Risk](https://img.shields.io/badge/risk-word_shifts-yellow)

- Issue: `SLLW` and `SRLW` depend on sorried bridge lemmas around bitvector
  arithmetic and bitmask behavior.
- Impact: recursive lowering proofs for word shifts cannot be closed cleanly.
- Response: isolate the bridge lemmas in small math-only files and prove the
  bitvector identities once.

### Trace Metadata Is Not Yet A Semantic Claim

![Risk](https://img.shields.io/badge/risk-trace_metadata-lightgrey)

- Issue: current Lean theorems generally prove semantic behavior, not exact
  agreement with Rust row metadata such as `virtual_sequence_remaining`,
  `is_first_in_sequence`, compression flags, or address metadata.
- Impact: exact trace-format faithfulness remains a separate theorem layer.
- Response: handle metadata after semantic lowering and memory-region work.

### Rust Expansion Is Coupled To Tracing Effects

![Risk](https://img.shields.io/badge/risk-rust_architecture-yellow)

- Issue: bytecode expansion, tracing, CPU execution, advice reads, virtual
  instruction behavior, and trace mutation are tightly coupled in Rust.
- Impact: Hax/Aeneas-style verification has to see too much effectful code at
  once.
- Response: split out a pure expansion API that produces an expanded sequence
  from an instruction, `xlen`, allocator state, and policy.

## Decisions

### Use Semantic Lowering Theorems

- Reason: source-level caller proofs should compose with final-row lowering
  theorems instead of duplicating recursive expansion inside every caller proof.

### Do Not Expand Every Caller From Scratch

- Reason: expanding every internal `SLLI`, `SLL`, `SRAI`, etc. inside each caller
  proof would duplicate proof work and make changes brittle.

### State Theorem Assumptions Explicitly

- Reason: the final theorem should say which subset is modeled: final recursive
  rows, ordinary RAM, advice assumptions, `rd = x0` policy, trap policy, and trace
  metadata scope.

## Risk Checklist

- [ ] Add owner for each red risk.
- [ ] Link each risk to the relevant theorem page.
- [ ] Decide which risks block the August completion claim.
