# Plan: Ordinary Memory Envelope

Status: ordinary-memory theorem boundary only for this version.

This note tracks the remaining memory-envelope work for bytecode expansion.
Ordinary load, store, and AMO equivalence proofs exist, but their theorem
boundary still needs a single clear statement of the memory assumptions under
which they apply.

Jolt special memory regions are explicitly out of scope for this version. We are
not proving that Rust/Jolt's memory implementation, address layout, or device
routing is correct.

## Core Point

For these Lean proofs, the trusted architectural side accesses memory through
`SailState`.

That means we should not try to model Rust's `JoltDevice` / `MemoryLayout` as
the main RAM predicate for this version. The Sail model sees memory as:

```lean
s.mem : ExtHashMap Nat (BitVec 8)
```

and the instruction semantics go through Sail's translation, PMP, PMA, MMIO,
alignment, and memory-read/write pipeline.

So the usable theorem envelope is not:

```text
address is inside Rust/Jolt RAM layout
```

It is a conditional ordinary-memory claim about the formal Jolt ISA:

```text
if the formal Jolt ISA expansion reaches ordinary memory rows such as LD/SD for
this access, and Sail treats the same bytes as ordinary non-MMIO memory available
in `s.mem`, then the bytecode expansion is equivalent to the Sail instruction.
```

That is already the shape of the existing assumptions.

## Current Pieces

The current memory setup is split across a global state predicate and
family-specific access bundles.

`JoltConfig s` gives global Sail execution assumptions:

- machine mode;
- `MPRV = 0`;
- populated `s.mem`.

`FlatPhysMem addr width s` is the read-side ordinary-memory predicate:

- load PMP check succeeds;
- `within_mmio_readable` returns `false`.

Loads add alignment/splitting facts through:

- `DwordLoadAssumptions`;
- `LoadReadAssumptions`.

Stores add write-side and read-modify-write assumptions through:

- `StoreFamily.FlatStoreMem`;
- `StoreFamily.FlatLoadStoreMem`;
- `StoreFamily.StoreMemoryAssumptions`.

AMOs add atomic access assumptions through:

- `AtomicFamily.FlatLoadStoreMem`;
- `AtomicFamily.FlatAtomicMem`;
- `AtomicFamily.AmoMemoryAssumptions`.

So there is no single RAM struct today. There is one common `JoltConfig`, one
common read predicate, and separate store/AMO bundles.

## What To Centralize

The useful cleanup is to centralize the Sail-pipeline ordinary-memory envelope,
not to introduce a Rust/Jolt layout model.

The target should be a shared access vocabulary, for example:

```text
SailOrdinaryReadMem addr width s
SailOrdinaryWriteMem addr width s
SailOrdinaryLoadStoreMem addr width s
SailOrdinaryAtomicMem op addr width s
```

or one namespace containing the existing equivalent structures.

The goal is mainly naming and reuse:

- avoid redefining `FlatStoreMem` separately for stores and atomics;
- avoid redefining `FlatLoadStoreMem` separately for stores and atomics;
- make public theorem statements read as ordinary Sail-memory assumptions;
- keep load/store/AMO proofs using the same operational memory vocabulary.

## What Not To Do In This Version

Do not add a Rust `JoltMemoryLayout` model for this version.

Do not attempt to classify addresses as input/advice/output/panic/termination
regions.

Do not prove compatibility between Rust `JoltDevice` behavior and Sail memory.
Do not claim Rust's memory implementation is correct.

Those are runtime/device-layer claims, not needed for the current conceptual
Jolt ISA bytecode-expansion theorem over ordinary memory-row execution.

## Milestones For This Version

1. Decide whether to keep the existing family-specific bundles or move the
   duplicate store/AMO structures into one shared memory module.
2. If centralizing, define shared read/write/load-store/atomic ordinary-memory
   predicates in `InstructionEquivalence.Memory`.
3. Re-export compatibility projections so existing load/store/AMO proofs do not
   need major rewrites.
4. Update planning/theorem comments to say "ordinary memory-row execution"
   rather than "Jolt RAM layout."
