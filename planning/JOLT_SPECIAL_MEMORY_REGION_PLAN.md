# Plan: Ordinary Memory Envelope

Status: ordinary-memory theorem boundary completed for load/store/AMO.

This note records the memory-envelope boundary for bytecode expansion. Ordinary
load, store, and AMO public equivalence theorems now take primitive-only family
bundles; internal exact access records are derived inside the proofs.

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

That is the theorem boundary implemented for loads, stores, and AMOs.

## Current Pieces

The current memory setup is split into primitive assumptions, public family
bundles, shared exact flat-memory predicates, and colocated helper contexts.

`JoltConfig s` gives only global Sail execution assumptions:

- machine mode;
- `MPRV = 0`.

Primitive memory assumptions live in `JoltBytecode.Assumptions`:

- `MemBytesPresent`;
- load/store/atomic PMP checks, including `*InRange` forms;
- readable/writable MMIO exclusion, including `*InRange` forms.

Shared exact flat-memory predicates live with the vmem helper lemmas in
`InstructionEquivalence.Memory.Utils`:

- `FlatPhysMem`;
- `FlatStoreMem`;
- `FlatLoadStoreMem`;
- `FlatAtomicMem`;
- `FlatLoadReservedMem`.

Public theorem bundles are family-local and primitive-only:

- `LoadFamily.LoadProgramEqSailAssumptions`;
- `StoreFamily.StoreProgramEqSailAssumptions`;
- `AtomicFamily.AmoDwordProgramEqSailAssumptions`;
- `AtomicFamily.AmoWordProgramEqSailAssumptions`.

Family-local helper contexts are not public theorem assumptions and live with
the helper lemmas that consume them:

- load no longer has a standalone helper context;
- `StoreFamily.StoreMemoryContext` lives in `StoreFamily.MemoryPipeline`;
- `AtomicFamily.AmoMemoryContext` lives in `AtomicFamily.Common`;
- `LoadReservedFamily.LoadReservedMemoryContext` lives in
  `LoadReservedFamily.Common`.

`InstructionEquivalence.Memory.Derived` contains only family-agnostic derivation
theorems from wider primitive windows to exact flat-access predicates. Family-specific
derivations live in the family `Derived.lean` files.

## What To Centralize

The useful cleanup was to centralize the Sail-pipeline ordinary-memory
vocabulary, not to introduce a Rust/Jolt layout model.

The implemented shared vocabulary is the `Flat*` exact flat-access family in
`InstructionEquivalence.Memory.Utils`.

The goal was mainly naming and reuse:

- stores and atomics share `FlatStoreMem` / `FlatLoadStoreMem`;
- public theorem statements expose primitive finite-window assumptions rather
  than internal pipeline helper contexts;
- load/store/AMO proofs use the same operational memory vocabulary.

## What Not To Do In This Version

Do not add a Rust `JoltMemoryLayout` model for this version.

Do not attempt to classify addresses as input/advice/output/panic/termination
regions.

Do not prove compatibility between Rust `JoltDevice` behavior and Sail memory.
Do not claim Rust's memory implementation is correct.

Those are runtime/device-layer claims, not needed for the current conceptual
Jolt ISA bytecode-expansion theorem over ordinary memory-row execution.

## Completed Milestones

1. Shared read/write/load-store/atomic ordinary-memory predicates live with the
   vmem helper lemmas in `InstructionEquivalence.Memory.Utils`.
2. Primitive finite-window assumptions centralized in `JoltBytecode.Assumptions`.
3. Load/store/AMO public theorem statements now take one primitive-only family
   bundle.
4. Shared helper contexts are colocated with the helper modules that consume
   them; no standalone adapter files remain.
