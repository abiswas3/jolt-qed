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

Sketch:

```lean
structure JoltMemoryLayout where
  ramStart : Nat
  heapEnd : Nat
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

Then define an address-range predicate:

```lean
def OrdinaryRamByte (layout : JoltMemoryLayout) (addr : Nat) : Prop :=
  layout.ramStart <= addr ∧ addr < layout.heapEnd

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

