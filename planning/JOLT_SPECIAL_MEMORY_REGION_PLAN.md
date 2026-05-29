# Plan: Jolt Special Memory Regions

This note records the current understanding and future plan for memory regions
that Rust/Jolt treats specially, while the imported Sail model only exposes a
hash-map memory.

## Core Point

We must not change the trusted Sail model.

Sail memory is just `s.mem : ExtHashMap Nat (BitVec 8)`. A guest RISC-V program
also has no concept of `JoltDevice`; it only performs loads and stores at
numeric addresses.

`JoltDevice` is a Rust emulator/tracer interpretation of certain address ranges:

- input
- trusted advice
- untrusted advice
- output
- panic
- termination
- zero-padding / below-RAM behavior

So the issue is not that these addresses cannot appear in Sail memory. They can.
The issue is that Rust/Jolt may interpret the same numeric address as device
state, while Sail interprets it as an ordinary hash-map byte.

## Current Theorem Scope

For now, the main load/store equivalence theorems should be understood as
ordinary-RAM theorems:

```text
if the architectural load/store address range is ordinary RAM,
then the Jolt bytecode expansion of the instruction matches Sail.
```

This is a valid and useful theorem envelope. It should be made explicit with a
Jolt-side memory-layout predicate.

Important wording: there is no primitive Jolt `LW` in the final bytecode trace.
Architectural `LW` is replaced by a sequence of Jolt/RISC-V/virtual
instructions. The theorem is about that expansion matching Sail `LW` under the
ordinary-RAM envelope.

## Short-Term Envelope

Introduce a Jolt-side memory-layout structure, without changing `SailState`.

The Rust source of truth is `common/src/jolt_device.rs::MemoryLayout::new`.
The layout is not just a bag of ranges; the order is part of the model:

1. All configurable sizes used below are rounded up to 8 bytes.
2. `trustedAdvice` and `untrustedAdvice` are placed below `RAM_START_ADDRESS`.
   The larger-or-equal advice region is placed first at the lower address.
3. `input` follows both advice regions.
4. `output` follows `input`.
5. `panic` is one full 8-byte word after `output`.
6. `termination` is one full 8-byte word after `panic`.
7. `ioEnd` follows `termination`.
8. The whole I/O block is padded down to a power-of-two number of 8-byte words;
   `lowestAddress = min trustedAdviceStart untrustedAdviceStart`.
9. Ordinary program RAM begins at `RAM_START_ADDRESS`; `stackEnd` is
   `RAM_START_ADDRESS + programSize`, and `heapEnd` is after the stack canary,
   stack, and heap.

In Lean we should first model an already-constructed layout plus a
well-formedness predicate containing these order/alignment facts.  A later
constructor theorem can prove that the Lean `mkLayout` function matches Rust's
`MemoryLayout::new`; the instruction proofs should depend only on
`WellFormedJoltMemoryLayout`, not on the constructor implementation.

Sketch:

```lean
structure JoltMemoryLayout where
  ramStart : Nat
  programSize : Nat
  maxTrustedAdviceSize : Nat
  maxUntrustedAdviceSize : Nat
  maxInputSize : Nat
  maxOutputSize : Nat
  stackSize : Nat
  heapSize : Nat
  heapEnd : Nat
  stackEnd : Nat
  trustedAdviceStart : Nat
  trustedAdviceEnd : Nat
  untrustedAdviceStart : Nat
  untrustedAdviceEnd : Nat
  inputStart : Nat
  inputEnd : Nat
  outputStart : Nat
  outputEnd : Nat
  panic : Nat
  termination : Nat
  ioEnd : Nat
```

```lean
def JoltMemoryLayout.lowestAddress (layout : JoltMemoryLayout) : Nat :=
  min layout.trustedAdviceStart layout.untrustedAdviceStart

structure WellFormedJoltMemoryLayout (layout : JoltMemoryLayout) : Prop where
  ramStart_eq : layout.ramStart = 0x80000000
  aligned8 :
    layout.trustedAdviceStart % 8 = 0 ∧
    layout.trustedAdviceEnd % 8 = 0 ∧
    layout.untrustedAdviceStart % 8 = 0 ∧
    layout.untrustedAdviceEnd % 8 = 0 ∧
    layout.inputStart % 8 = 0 ∧
    layout.inputEnd % 8 = 0 ∧
    layout.outputStart % 8 = 0 ∧
    layout.outputEnd % 8 = 0 ∧
    layout.panic % 8 = 0 ∧
    layout.termination % 8 = 0 ∧
    layout.ioEnd % 8 = 0 ∧
    layout.ramStart % 8 = 0
  advice_order :
    (layout.maxTrustedAdviceSize >= layout.maxUntrustedAdviceSize →
      layout.trustedAdviceStart = layout.lowestAddress ∧
      layout.trustedAdviceEnd = layout.untrustedAdviceStart) ∧
    (layout.maxTrustedAdviceSize < layout.maxUntrustedAdviceSize →
      layout.untrustedAdviceStart = layout.lowestAddress ∧
      layout.untrustedAdviceEnd = layout.trustedAdviceStart)
  input_after_advice :
    layout.inputStart = max layout.trustedAdviceEnd layout.untrustedAdviceEnd
  output_after_input : layout.outputStart = layout.inputEnd
  panic_after_output : layout.panic = layout.outputEnd
  termination_after_panic : layout.termination = layout.panic + 8
  io_after_termination : layout.ioEnd = layout.termination + 8
  io_below_ram : layout.ioEnd <= layout.ramStart
  ram_shape :
    layout.stackEnd = layout.ramStart + layout.programSize ∧
    layout.stackEnd <= layout.heapEnd
```

Then define byte and access classification predicates:

```lean
inductive JoltAddressClass where
  | ordinaryRam
  | trustedAdvice
  | untrustedAdvice
  | input
  | output
  | panic
  | termination
  | zeroPadding
  | unsupported

def OrdinaryRamByte (layout : JoltMemoryLayout) (addr : Nat) : Prop :=
  layout.ramStart <= addr ∧ addr < layout.heapEnd

def InHalfOpen (addr start stop : Nat) : Prop :=
  start <= addr ∧ addr < stop

def InputByte (layout : JoltMemoryLayout) (addr : Nat) : Prop :=
  InHalfOpen addr layout.inputStart layout.inputEnd

-- Similar predicates for trusted advice, untrusted advice, output, panic,
-- termination, and zero-padding.

structure OrdinaryRamAccess
    (layout : JoltMemoryLayout) (addr : BitVec 64) (width : Nat) : Prop where
  noOverflow : addr.toNat + (width - 1) < 2 ^ 64
  allBytesRam :
    ∀ i, i < width →
      OrdinaryRamByte layout ((addr + BitVec.ofNat 64 i).toNat)
```

This should be bundled with existing memory assumptions such as
`BareTranslation`, `FlatPhysMem`, alignment, and populated memory.

The point is to state explicitly that current load/store proofs apply only when
Rust/Jolt would route the access to ordinary RAM.

For load-family expansion proofs, distinguish the architectural access from the
Jolt expansion access.  RV64 `LW` is the important example:

```text
Sail architectural access:  ea, width 4
Jolt expansion access:      ea & -8, width 8
```

So the ordinary-RAM envelope for `LW` should require both:

```lean
OrdinaryRamAccess layout ea 4
OrdinaryRamAccess layout (ea &&& (-8 : BitVec 64)) 8
```

Eventually we can prove the second from the first plus 8-byte-aligned region
boundaries, but keeping both in the first theorem statement is clearer and
closer to the actual Rust over-read.

## Future Device-Region Coverage

To cover guest loads from input/advice/output/panic/termination regions, add a
Jolt-side device model, still without changing Sail.

Sketch:

```lean
structure JoltDeviceState where
  layout : JoltMemoryLayout
  inputs : Nat → BitVec 8
  trustedAdvice : Nat → BitVec 8
  untrustedAdvice : Nat → BitVec 8
  outputs : Nat → BitVec 8
  panic : Bool
```

Define a JoltDevice-style byte source:

```lean
def DeviceLoadByte (dev : JoltDeviceState) (addr : Nat) : BitVec 8 :=
  -- mirror Rust JoltDevice::load:
  -- input/advice/output arrays, panic flag, termination zero, zero-padding.
  sorry
```

Then relate Sail memory to device state by an invariant:

```lean
def SailMemMirrorsDeviceReads
    (s : SailState) (dev : JoltDeviceState) : Prop :=
  ∀ addr,
    IsReadableDeviceAddress dev.layout addr →
      s.mem.get? addr = some (DeviceLoadByte dev addr)
```

For equivalence to Sail `execute_LOAD`, device-read coverage also needs Sail to
treat those numeric addresses as normal readable memory, not Sail MMIO:

```lean
within_mmio_readable (physaddr.Physaddr addr) width s = .ok false s
```

This is easy to miss: Rust/Jolt special regions are not Sail CLINT/HTIF MMIO.
They are Jolt emulator/tracer regions.  The first useful device theorem should
therefore be:

```text
if Sail memory mirrors the JoltDevice byte source
and Sail does not route the address through Sail MMIO
and the Jolt expansion's 8-byte read is valid in the same Jolt region,
then the existing bit-extraction proof still goes through.
```

The separate Sail-MMIO case should remain outside the equivalence theorem until
we intentionally define compatibility between Sail's width-sensitive MMIO read
and Jolt's 8-byte expansion read.

For most load-region proofs, the existing bit-extraction arguments should not
change. The only changed premise is the byte source:

```text
ordinary RAM: s.mem[addr]
device read:  DeviceLoadByte dev addr, with s.mem mirroring it
```

This suggests factoring load decomposition proofs over an abstract byte source:

```lean
byteAt : Nat → BitVec 8
```

Then instantiate `byteAt` for ordinary RAM and for each readable device region.

## Expected Case Split

Full JoltDevice coverage will eventually need address-class cases:

- ordinary RAM
- input reads
- trusted advice reads
- untrusted advice reads
- readable output reads
- panic reads
- termination reads
- zero-padding reads
- output writes
- panic writes
- termination writes
- illegal or unsupported regions

Load cases should mostly share proof structure after factoring over `byteAt`.
Store/output/panic/termination cases are more different because Rust mutates
device state, not just memory.

## Practical Milestones

1. Add a Jolt memory-layout type and ordinary-RAM access predicate.
2. Update load/store theorem statements to use the ordinary-RAM envelope.
3. Keep current proofs semantically unchanged, but make their scope explicit.
4. Later, introduce a Jolt device-state model for special regions.
5. Factor load proofs over an abstract byte source before adding all device
   read cases.
6. Treat output/panic/termination writes as a separate runtime/device theorem
   layer, not as plain Sail-memory equivalence.
