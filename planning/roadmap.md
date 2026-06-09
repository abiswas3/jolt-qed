# Roadmap

This is the current bytecode-expansion roadmap after the June 2026 risk audit.
It intentionally excludes lookup-table verification.

The primary target is Jolt as a formal/conceptual bytecode-expansion model, not
a full verification of the current Rust implementation. Rust code is useful as
design evidence and implementation context, but exact Rust conformance is a
separate downstream claim.

The core object is the Lean Jolt ISA: a final-row instruction set that is partly
ordinary RISC-V-style rows and partly Jolt-specific virtual rows. Sail is the
trusted RISC-V reference semantics. The main theorem shape is:

```text
formal Jolt ISA expansion semantics = Sail architectural instruction semantics
```

We should not axiomatize Jolt runtime/device memory as equal to Sail memory. That
would assume away a separate runtime/device correctness problem rather than
prove bytecode-expansion correctness.

Target: bytecode expansion complete by August 2026.

## Current Status

The Lean bytecode model now builds as a final-row Jolt model, not just a
source-expansion sketch:

- recursive inline expansion is handled by using final trace-row instructions
  and expansion blocks;
- virtual-register numbers follow Rust's allocator layout directly;
- ordinary loads `LB/LBU/LH/LHU/LW/LWU` are proved;
- ordinary stores `SB/SH/SW` are proved;
- word-shift proof holes are closed in the root build;
- most AMO word/dword equivalence proofs are present in the root build;
- `MULHSU` is included in the root build.

`lake build JoltBytecode` succeeds.

## Feedback Flags

| Issue | Status |
| --- | --- |
| `CSRRS` | ![User will fix](https://img.shields.io/badge/status-user_will_fix-brightgreen) |
| Side-effecting `rd = x0` | ![Open](https://img.shields.io/badge/status-open-red) Accepted as a real in-scope issue |
| Advice tape | ![Needs feedback](https://img.shields.io/badge/status-not_yet_settled-yellow) |
| Trap/failure boundary | ![Needs feedback](https://img.shields.io/badge/status-not_yet_settled-yellow) |
| Trace metadata | ![Needs feedback](https://img.shields.io/badge/status-not_yet_settled-yellow) Non-blocking for semantic equivalence |
| LR/SC reservation semantics | ![Deferred](https://img.shields.io/badge/status-deferred-lightgrey) Not provable against current Sail hooks |
| Jolt special memory regions | ![Out of scope](https://img.shields.io/badge/status-out_of_scope-lightgrey) Not part of this version |
| Exact Rust implementation conformance | ![Out of scope](https://img.shields.io/badge/status-out_of_scope-lightgrey) Optional downstream layer |

## Closed Workstreams

### Compositional Lowering

Status: closed.

Closed by restricting `JoltISA.Instr` to final trace-row instructions and using
expansion blocks for source instructions that inline recursively.

### Virtual-Register Layout

Status: closed for Lean-side modeling.

`JoltBytecode.JoltISA.VirtualRegisters` models Rust's absolute virtual-register
layout:

- `32..39`: reserved persistent virtual registers;
- `40..47`: Rust `allocate()` scratch pool;
- `48..`: Rust `allocate_for_inline()` pool.

The load/store/system/AMO programs use those absolute registers directly. A
generic renaming theorem is no longer the intended fix.

### Stores

Status: closed for ordinary `SB`, `SH`, and `SW`.

The ordinary store proofs include read-modify-write splice reasoning and are
included in the root build.

### Atomics

Status: mostly closed.

The roadmap entry saying atomics were missing is stale. The root build imports
the current AMO word/dword theorem files. The separate LR/SC family is still
open because it depends on reservation semantics; see below.

## Remaining Lean-Side Risks

### Ordinary Sail-Memory Envelope

Status: discussed; cleanup optional.

Current load/store/AMO theorems rely on flat, ordinary-memory assumptions. The
ordinary Sail-memory theorem envelope still needs to be made explicit and
centralized.

This is not a proof that Rust/Jolt memory is correct. The intended claim is
conditional: if the formal Jolt ISA expansion reaches ordinary memory rows such
as `LD`/`SD`, and Sail treats the same bytes as ordinary non-MMIO memory, then
the expansion is equivalent to Sail.

Jolt special memory regions are not planned for this version.

See: `planning/JOLT_SPECIAL_MEMORY_REGION_PLAN.md`

### LR/SC Reservation Semantics

Status: deferred.

`LR.W`, `LR.D`, `SC.W`, and `SC.D` intentionally do not have active closed
`*_Program_eq_sail` theorem fronts. The generated Sail model exposes reservation
behavior through opaque hooks such as `load_reservation`, `match_reservation`,
and `cancel_reservation`, while Jolt models reservations through concrete
virtual registers and advised success bits.

These cannot be proved against the current Sail model without adding a trusted
reservation-state contract or switching to a Sail model with visible reservation
state. They are deferred for this version.

### `rd = x0` Policy

Status: open for side-effecting instructions.

Pure writeback-only instructions can use Rust's no-op replacement path. The
remaining issue is side-effecting instructions where Rust remaps the writeback
to a virtual register so side effects still occur.

### Advice Tape

Status: not yet settled.

Lean advice-load theorems use explicit advice values. Rust reads bytes from a
mutable FIFO advice tape. The tape cursor, byte packing, depletion, and underflow
behavior are not yet modeled.

### Trap/Failure Boundary

Status: not yet settled.

Some current theorem statements compare Jolt failures with Sail architectural
exceptions. The final claim needs to say clearly whether it covers architectural
trap equivalence, trace accept/reject behavior, or only the aligned,
non-trapping ordinary Sail-memory subset.

### CSR Coverage

Status: ![User will fix](https://img.shields.io/badge/status-user_will_fix-brightgreen)

`CSRRW` is proved. `CSRRS` is expected to be added soon and is still not imported
in the root build.

### Trace Metadata

Status: not yet settled; non-blocking for semantic equivalence.

Current theorems prove architectural effect, not exact row metadata such as
`virtual_sequence_remaining`, `is_first_in_sequence`, compression flags, or PC
metadata.

See: `planning/JOLT_TRACE_METADATA_PLAN.md`

## Out-Of-Scope Implementation Claims

### Exact Rust Expansion Provenance

Status: out of scope for the core Lean theorem.

Lean can prove the semantics of the expansion definitions in this repository.
It does not need to prove that those definitions were copied from the current
Rust source in order to establish the conceptual Jolt expansion theorem.

If exact implementation conformance later becomes a goal, that requires
Rust-side support such as a generated expansion manifest, golden tests, or an
exported pure expansion API. That is not a Lean-side risk for this version.
