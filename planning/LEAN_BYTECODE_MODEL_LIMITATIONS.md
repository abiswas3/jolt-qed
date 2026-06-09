# Current Jolt ISA Correctness Risk Audit

This note records the current Lean-side risks after the June 2026
bytecode-expansion audit. It supersedes the older audit language that described
recursive expansion, virtual-register allocation, stores, and word-shift bridge
lemmas as open Lean proof risks.

The project is primarily about correctness of the formal/conceptual Jolt ISA.
Bytecode expansion is the mechanism being proved. This is not, in this version,
a proof that the current Rust implementation matches the Lean definitions
line-for-line.

The core object is the Lean Jolt ISA: a final-row instruction set that is partly
ordinary RISC-V-style rows and partly Jolt-specific virtual rows. Sail is the
trusted RISC-V reference semantics. The main theorem compares this formal Jolt
ISA semantics with Sail, instruction by instruction.

We should not add an axiom saying Jolt runtime/device memory equals Sail memory.
That would defeat the point of the theorem by assuming away a separate
runtime/device correctness problem.

This document intentionally excludes lookup-table verification.

## Build Status

`lake build JoltBytecode` succeeds.

There are no active `sorry` or `admit` holes in
`JoltBytecode/InstructionEquivalence`; the only hits are comments describing
intentionally omitted theorem fronts.

`JoltBytecode.InstructionEquivalence.ALUFamily.Mult.Mulhsu` is included in the
root build.

## Closed Or Reclassified Risks

### Recursive Expansion / Final Rows

Status: closed for the current Lean model.

The current Jolt ISA programs use final trace-row instructions and expansion
blocks for recursively inlined source instructions. The old concern that Lean
only proved source-level `emit_*` sequences is no longer the right description
of the root proof surface.

### Virtual Registers

Status: closed for Lean-side modeling.

Lean models Rust's absolute virtual-register layout in
`JoltBytecode.JoltISA.VirtualRegisters`:

- registers `32..39` are reserved persistent virtual registers;
- registers `40..47` are Rust's instruction-local `allocate()` scratch pool;
- registers `48..` are Rust's larger inline allocation pool.

The modeled expansions use these absolute Rust register numbers directly, so a
generic renaming theorem is not the planned Lean-side fix.

Exact Rust provenance is not part of the core theorem. If later work wants to
prove that the Rust implementation emits exactly these rows, that belongs to a
separate Rust-side conformance layer, not to the Lean virtual-register model.

### Ordinary Stores

Status: closed.

`SB`, `SH`, and `SW` equivalence proofs are in the root build. The old store
proof-hole language is stale.

### Word Shifts

Status: closed in the root build.

`SLLW` and `SRLW` are imported by `JoltBytecode.lean`, and the instruction
equivalence tree has no active proof holes.

### Atomics

Status: mostly closed.

The root build imports the current AMO word/dword theorem files. This does not
cover LR/SC reservation behavior, which remains separate and open.

### Advice Values / Rust Advice Tape

Status: reclassified for the core theorem.

The formal Jolt ISA may take advice as explicit values/oracles for Jolt-specific
rows. That is not itself a Lean-side correctness gap. The in-scope obligation is
to prove that the advice-backed row sequence, under its guards and assumptions,
matches the trusted Sail architectural instruction.

Rust's mutable byte FIFO advice tape is a separate implementation-conformance
claim. Modeling its byte packing, cursor movement, depletion, and underflow
behavior would help prove that the current Rust implementation supplies the same
advice values, but it is not required for the conceptual Jolt ISA theorem.

## Remaining Lean-Side Risks

### 1. Ordinary Sail-Memory Envelope

Status: discussed; cleanup optional.

Current issue: the memory theorem boundary is still too implicit in naming.

The load/store/AMO proofs assume a flat, populated, machine-mode memory setting
through predicates such as `JoltConfig`, `BareTranslation`, and `FlatPhysMem`.
Rust/Jolt also has device-like regions for input, trusted advice, untrusted
advice, output, panic, termination, and zero-padding behavior.

Special memory regions are out of scope for this version. The in-scope work is
only to state the ordinary Sail-memory envelope explicitly.

This is not a proof that Rust/Jolt's memory implementation is correct. The
intended theorem is conditional: if the formal Jolt ISA expansion reaches
ordinary memory rows such as `LD`/`SD`, and Sail treats the same bytes as
ordinary non-MMIO memory in `SailState`, then the expansion is equivalent to the
trusted Sail instruction.

Required Lean-side work:

- define a central ordinary Sail-memory access predicate;
- use it consistently in load/store/AMO theorem statements;
- clearly distinguish ordinary memory from Jolt special regions;
- state that special-region equivalence is not part of this version.

See `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`.

### 2. LR/SC Reservation Semantics

Status: deferred.

`LR.W`, `LR.D`, `SC.W`, and `SC.D` do not have active closed equivalence theorem
fronts.

The Rust-faithful Jolt expansions model reservations concretely with virtual
registers and advised success bits. The generated Sail model uses opaque hooks:

```text
load_reservation
match_reservation
valid_reservation
cancel_reservation
```

Those hooks do not expose reservation state through `SequentialState`, so the
current Sail model does not provide enough visible state to prove the Jolt
reservation model equivalent.

These cannot be proved against the current Sail model. Closing them would
require one of:

- either add a trusted reservation-state contract relating Sail hooks to Jolt
  reservation virtual registers;
- or use a Sail model where reservation state is visible enough to reason about.

Until then, LR/SC should be listed as a deferred proof-boundary exception, not as
in-scope Lean work for this version.

### 3. `rd = x0` Policy For Side-Effecting Instructions

Status: open; accepted as a real in-scope issue.

Current issue: the pure writeback-only case is handled, but side-effecting cases
remain and are a real in-scope issue.

Rust treats `rd = x0` specially:

- pure writeback-only instructions can be replaced by a no-op;
- side-effecting instructions still need to perform their effects, so Rust may
  remap the destination to a temporary virtual register and discard the final
  architectural writeback.

Required Lean-side work:

- classify remaining instructions by Rust `rd = x0` behavior;
- add theorem fronts for side-effecting remap cases;
- avoid theorem statements that silently assume away Rust dispatch behavior.

### 4. Trap / Failure Boundary

Status: not yet settled.

Current issue: theorem statements need to be explicit about the kind of failure
being compared.

Some Lean memory proofs compare Jolt failures with Sail architectural memory
exceptions. Rust inline sequences can also use virtual assertions that fail the
trace. Those are not automatically the same semantic object.

Required decision:

- prove architectural exception equivalence;
- prove trace accept/reject behavior;
- or restrict the main theorem to an aligned, non-trapping ordinary Sail-memory
  subset and handle rejected traces separately.

### 5. CSR Coverage

Status: ![User will fix](https://img.shields.io/badge/status-user_will_fix-brightgreen)

Current issue: `CSRRW` is proved, but `CSRRS` is still commented out in
`JoltBytecode.lean`. It is expected to be added soon.

Required Lean-side work:

- prove and root-import the `CSRRS` equivalence theorem if CSRRS is in the
  bytecode-expansion scope.

### 6. Trace Metadata

Status: not yet settled; non-blocking for semantic equivalence.

Current issue: the semantic instruction-equivalence theorems do not prove exact
trace-row metadata agreement with Rust.

This is not a blocker for architectural semantic equivalence, but it remains a
separate trace-format theorem layer.

See `planning/JOLT_TRACE_METADATA_PLAN.md`.

## Out-Of-Scope Implementation Claims

### Exact Rust Expansion Provenance

Lean proves semantic facts about the Lean expansion definitions as the formal
Jolt bytecode-expansion model. It does not, in this version, prove that the
current Rust implementation emits exactly those definitions.

If exact Rust conformance becomes a target, it will require Rust-side support,
for example:

- a generated expansion manifest;
- golden tests that dump final expanded rows;
- a pure Rust expansion API that Lean tooling can consume;
- CI that detects when Rust expansion output changes without updating Lean.

This is not a Lean proof obligation for the conceptual Jolt theorem and should
not be described as a remaining virtual-register modeling risk.

### Rust Byte Advice Tape

The Rust byte tape is an implementation mechanism for supplying advice. The
core theorem can quantify over explicit advice values as part of the formal Jolt
ISA semantics.

If exact Rust conformance becomes a target, then the Rust-side layer should
prove that tape bytes, cursor state, packing, depletion, and underflow behavior
produce the same advice values assumed by the Lean theorem. That is not a
required Lean-side risk for this version.

## Current Claim Stack

The current Lean work proves the conceptual bytecode-expansion theorem:

```text
formal final-row Jolt ISA semantics
  with explicit advice values/oracles where needed
  =
Sail architectural instruction semantics
```

for the covered instructions and under the theorem assumptions.

The remaining work is to make the theorem envelope explicit. Exact Rust
implementation conformance is a separate optional layer:

```text
formal final-row Jolt expansion semantics
  = proved in Lean
Sail architectural semantics
  = trusted imported Sail model

optional later:
Rust expansion output
  = formal final-row Jolt expansion definitions
```
