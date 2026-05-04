# Roadmap

This is a skeleton roadmap for bringing the Lean bytecode-expansion model to a
complete, Rust-faithful state.

Target: bytecode expansion complete by August 2026.

Paper target: CCS / USENIX Security / IEEE S&P submission track, assuming the
Rust tracer interface and instruction expansion code remain stable.

## Scope

Bytecode expansion completeness means:

- covered architectural instructions have Lean models matching the Rust tracer
  expansion semantics;
- recursive inline expansion is handled compositionally by lowering theorems;
- missing store and atomic instruction families are covered;
- memory assumptions are explicit, including ordinary RAM versus Jolt special
  regions;
- known theorem-boundary issues are either fixed or clearly documented.

## Workstreams

### 1. Compositional Lowering

Status: planned.

Goal: prove lowering theorems once for recursively expanding instructions, then
reuse them in caller proofs instead of expanding every caller manually.

See: `docs/JOLT_COMPOSITIONAL_LOWERING_PLAN.md`

### 2. Loads and Special Memory Regions

Status: planned.

Goal: make the ordinary-RAM theorem envelope explicit, then later add coverage
for readable JoltDevice regions such as input/advice/output/panic/termination.

See: `docs/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`

### 3. Stores

Status: incomplete.

Goal: finish `SW`, `SH`, and `SB` expansion proofs, including read-modify-write
splice lemmas and the relevant memory envelope.

### 4. Atomics

Status: missing.

Goal: add bytecode expansion models and equivalence theorems for the atomic
instruction family used by the Rust tracer.

### 5. `rd = x0` Policy

Status: planned.

Goal: model Rust's dispatch policy for `rd = x0`: no-op replacement for pure
writeback instructions, virtual-register remapping for side-effecting
instructions, and special-case handling where needed.

### 6. Advice Tape

Status: later.

Goal: connect explicit Lean advice values to Rust's byte-oriented advice/device
state.

### 7. Trace Metadata

Status: later.

Goal: separately verify row metadata such as `virtual_sequence_remaining`,
`is_first_in_sequence`, compression flags, and address metadata.

See: `docs/JOLT_TRACE_METADATA_PLAN.md`

### 8. Virtual Register Renaming

Status: later.

Goal: prove a renaming-invariance theorem connecting fixed Lean virtual-register
templates to Rust allocator-chosen virtual registers.

See: `docs/JOLT_VIRTUAL_REGISTER_RENAMING_PLAN.md`

## Milestones

### May 2026

- Freeze and document theorem envelopes.
- Add missing compositional lowering theorem variants for common virtual and
  real/virtual boundary cases.
- Start closing store proof gaps.

### June 2026

- Finish store-family proof obligations.
- Add ordinary-RAM memory envelope consistently across load/store theorems.
- Begin atomics coverage.

### July 2026

- Complete atomics.
- Add device-region read plan or initial readable-region proofs.
- Sweep recursive lowering coverage for instructions used inside loads, stores,
  advice, and atomics.

### August 2026

- Close remaining bytecode-expansion coverage gaps.
- Run a theorem/status audit against the Rust tracer instruction directory.
- Produce a coverage table:

```text
Rust instruction
  -> source inline sequence
  -> recursively lowered sequence
  -> Lean semantic model
  -> theorem status
```
