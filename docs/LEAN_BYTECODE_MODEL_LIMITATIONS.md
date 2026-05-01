# Notes for Ari: Current Lean Model vs. Rust Bytecode Expansion

This is a short audit note on the current `JoltBytecode/EmbeddedSailJoltState`
formalization on `ari/sail-to-jolt`, compared against the checked-out Rust Jolt
tree at `/Users/quang.dao/Documents/SNARKs/jolt`.

The main takeaway is positive but important to state precisely: the current Lean
model is strongest as a semantic/source-expansion model. It is not yet a fully
faithful model of the final Rust bytecode rows produced after recursive inline
expansion.

## What Looks Faithful

The recent ALU advice-family work looks closely aligned with the current Rust
source-level `emit_*` sequences:

- `DIV`, `DIVU`, `DIVW`, `DIVUW`
- `REM`, `REMU`, `REMW`, `REMUW`

In particular, the current Rust `DIVW`/`REMW` code now uses the `SRAI ..., 32`
remainder-canonicality check, matching the Lean model. The older bug report that
describes `SRAI ..., 31` appears stale relative to the current Rust tree.

The theorem shape is also sensible:

- completeness: honest advice makes the Jolt sequence run successfully and match
  Sail;
- soundness for `DIV`/`DIVU`/`DIVW`: successful arbitrary advice pins down the
  honest advice;
- soundness for `DIVUW` and the `REM*` family: successful arbitrary advice pins
  down the architectural writeback state, even when raw advice uniqueness is too
  strong.

That last weakening is especially appropriate for `DIVUW`, where non-canonical
64-bit quotient advice can share the same low 32 bits and still produce the
correct architectural writeback.

## The Main Limitation: Recursive Expansion

Rust inline expansion is recursive. Inside `InstrAssembler::add_to_sequence`, an
emitted instruction is not appended directly; instead Rust appends
`inst.inline_sequence(...)`.

So a source-level expansion like:

```text
SLLI v0, v0, 3
SLL  v1, v1, v0
SRAI rd, v1, 56
```

does not necessarily appear as those three final bytecode rows. In the current
Rust tree:

- `SLLI` lowers to `VirtualMULI`;
- `SLL` lowers to `VirtualPow2; MUL`;
- `SRAI` lowers to `VirtualSRAI` with a computed bitmask.

For example, RV64 `LB` source expansion emits:

```text
ADDI v0, rs1, imm
ANDI v1, v0, -8
LD   v1, v1, 0
XORI v0, v0, 7
SLLI v0, v0, 3
SLL  v1, v1, v0
SRAI rd, v1, 56
```

The Lean model mirrors this source-level sequence using helpers such as
`vreg_SLLI`, `vreg_SLL`, and `vreg_SRAI_to_real`. That is likely semantically
right, but it is not a proof about the final recursively expanded bytecode rows.

This gap matters because bugs can live in the recursive lowering layer:

- an incorrect lowering of `SLLI`, `SLL`, `SRAI`, etc.;
- incorrect temporary virtual-register allocation during recursive expansion;
- incorrect `virtual_sequence_remaining` metadata;
- mismatch between source-level helper semantics and final virtual primitive
  semantics;
- operand or writeback differences that preserve final architectural state but
  differ from the actual bytecode trace.

The gap is largest for loads, stores, advice loads, and any expansion containing
shift operations. The ALU advice-family division/remainder files are closer to
the Rust source expansion, but they still inherit any mismatch in emitted
sub-instructions that recursively lower further.

## Other Important Boundaries

### `rd = x0`

Many Lean equivalence theorems assume `rd != x0`. Rust has special handling for
`rd = x0`, including replacing no-side-effect instructions with a no-op or
remapping side-effecting writes to temporary virtual registers. That behavior is
mostly outside the current Lean theorem boundary.

### Virtual Register Allocation

Lean commonly hardcodes virtual register names such as `0`, `1`, `2`, etc. Rust
uses an allocator with reserved virtual-register ranges and inline temporaries.
This is probably semantically harmless when registers are fresh and disjoint,
but the formal connection needs either:

- parameterized Lean expansions over allocator outputs; or
- a renaming-invariance theorem connecting the hardcoded Lean names to Rust's
  allocated names.

### Memory, Traps, and Alignment

The load proofs assume a flat, well-behaved memory setup through predicates such
as `JoltConfig`, `BareTranslation`, and `FlatPhysMem`. Rust's tracer has MMU,
device ranges, advice regions, panic/output/termination mappings, and trap
behavior.

There is also an operational mismatch around misalignment: Lean sometimes models
misaligned loads as an architectural memory exception, while Rust inline
sequences use virtual assertion instructions that panic/fail the trace.

### Advice Tape

Lean treats advice as explicit `BitVec` parameters. Rust `VirtualAdviceLoad`
reads little-endian bytes from a mutable advice tape and can fail if insufficient
bytes are present. Tape ordering, byte packing, depletion, and width
canonicality are not currently part of the Lean model.

### Store Proofs and Remaining Holes

Stores are not yet at the same maturity level as the division/remainder advice
family. `SB` and `SH` still have top-level proof holes, and `SW` has partial
store-pipeline obligations remaining.

Known proof holes also remain in the word-shift bridge lemmas for `SLLW` and
`SRLW`.

## Suggested Path Forward

It would help to split the Rust code so bytecode expansion is independently
verifiable:

1. A small base crate for instruction formats, normalized instructions, virtual
   registers, and expansion metadata.
2. A pure bytecode-expansion crate:

   ```text
   expand(instr, xlen, allocator_state) -> Result<ExpandedSequence, ExpansionError>
   ```

   This crate should avoid CPU mutation, MMU behavior, advice tape reads,
   tracing side effects, and panic-based control flow.

3. A tracer crate that consumes expanded bytecode and handles CPU state, memory,
   MMU, advice tape, host I/O, and trace side effects.

With that split, the proof story can become layered:

- verify the bytecode expander, possibly with Hax or Aeneas, against a Lean
  expansion spec;
- prove the final primitive bytecode rows implement the intended source-level
  expansion semantics;
- connect those source-level semantics to Sail architectural semantics, where
  the current Lean work already provides a strong start.

In the short term, a mechanical coverage table would be very useful:

```text
Rust instruction
  -> source inline sequence
  -> final recursively expanded bytecode rows
  -> Lean definition
  -> theorem status
```

That table would make it much easier to distinguish "semantically proven",
"source-expansion proven", "final-bytecode proven", and "not yet covered".

## Making the Formalization More Realistic

This section sketches concrete fixes for the limitations above. Some are fairly
local proof-engineering tasks; others are better treated as Rust architecture
work before trying to verify them.

### 1. Model Recursive Expansion Explicitly

Current issue: many Lean definitions model the source-level `emit_*` sequence,
while Rust recursively lowers each emitted instruction through
`inst.inline_sequence(...)`.

Path forward:

- Introduce two Lean levels:
  - `sourceInline : Instr -> List Instr`, mirroring the human-written Rust
    `emit_*` sequence.
  - `lowerInline : Instr -> List PrimitiveInstr`, recursively expanding until
    only final bytecode primitives remain.
- Prove a lowering theorem:

  ```text
  denote (lowerInline instr) = denote (sourceInline instr)
  ```

  for each instruction whose source sequence contains recursively lowered
  sub-instructions.
- For shift-heavy code, add focused theorems for the recursive pieces first:
  - `SLLI` lowers to `VirtualMULI`;
  - `SLL` lowers to `VirtualPow2; MUL`;
  - `SRAI` lowers to `VirtualSRAI` with the computed bitmask;
  - similarly for `SRLI`, `SRA`, `SRL`, and word variants.

This is a clear path and should be tractable, but it is not tiny. The first
useful milestone would be to make `LB` or `LW` fully final-bytecode faithful,
because those exercise recursive shift lowering and memory access together.

### 2. Generate an Expansion Manifest From Rust

Current issue: the correspondence between Rust and Lean is checked manually.

Path forward:

- Add a Rust test/tool that serializes, for each instruction and representative
  operand shape:

  ```text
  instruction name
  xlen
  source operands
  source inline sequence
  final recursively expanded sequence
  virtual_sequence_remaining metadata
  allocated virtual registers
  ```

- Commit the output as a golden manifest, or generate it in CI.
- In Lean, either:
  - consume the manifest as data and prove semantic facts about the listed rows;
    or
  - generate Lean definitions from the manifest.

This is one of the highest-leverage near-term fixes. Even before full formal
verification, it would expose drift immediately when Rust expansion changes.

### 3. Parameterize Virtual Register Allocation

Current issue: Lean hardcodes virtual registers like `0`, `1`, `2`, while Rust
uses an allocator with reserved ranges and inline temporaries.

Path forward:

- Define a Lean `AllocatorState` and make expansions take explicit allocated
  registers:

  ```text
  jolt_lb (temps : LBTemps) ...
  ```

  where `LBTemps` contains fields such as `v0`, `v1`, plus freshness/disjointness
  proofs.
- Alternatively, keep the current hardcoded definitions but prove a general
  virtual-register renaming theorem:

  ```text
  if rho is injective on the registers touched by program p,
  then running rename(rho, p) is equivalent to running p under renamed vregs.
  ```

The renaming theorem is elegant and would preserve the current readable proofs.
Parameterizing every definition is more mechanical but may make proofs noisier.
The best route is probably to prove renaming once and then use the current
hardcoded programs as canonical templates.

### 4. Cover `rd = x0`

Current issue: many Lean theorems assume `rd != x0`, while Rust has explicit
special handling for `rd = x0`.

Path forward:

- First classify instructions by Rust behavior when `rd = x0`:
  - pure no-side-effect instructions lowered to no-op;
  - side-effecting instructions whose destination is remapped to a virtual
    register so the side effects still occur;
  - instructions where `rd` is not meaningful.
- Add a Lean wrapper theorem for the Rust dispatch layer:

  ```text
  expandWithX0Policy instr = ...
  ```

- Prove per-class lemmas:
  - no-op replacement preserves architectural state for pure writeback-only
    instructions;
  - remapping preserves side effects while discarding the architectural writeback.

This is conceptually straightforward, but it touches many instructions. A useful
first pass is a coverage table showing which Lean theorem currently depends on
`rd != x0` and what Rust does in that case.

### 5. Separate Trace Failure From Architectural Traps

Current issue: some Lean load proofs model misalignment as a Sail
`Memory_Exception`, while Rust inline sequences often use virtual assertions
that panic/fail the trace.

Path forward:

- Decide and document the target semantics for bytecode expansion:
  - architectural equivalence including traps; or
  - prover/tracer accept-reject behavior; or
  - equivalence only under preconditions excluding traps and assertion failures.
- If the target is accept-reject behavior, add a Lean result type that
  distinguishes:

  ```text
  RetireSuccess
  ArchitecturalException
  AssertionFailure
  HostFailure
  ```

- If the target is only well-formed Jolt executions, strengthen theorem
  preconditions to exclude misalignment, MMIO/device regions, and other trap
  cases, then remove the misleading appearance of proving those cases.

The shortest realistic path is probably preconditioned equivalence for now:
prove final bytecode matches Sail on the flat, aligned, non-trapping subset.
Later, add a separate theorem about rejected traces.

### 6. Make Memory Assumptions an Explicit Semantic Envelope

Current issue: Lean assumes a flat, populated, machine-mode memory setting, but
Rust has MMU/device/advice/host regions.

Path forward:

- Create a single documented predicate, perhaps:

  ```lean
  JoltFlatMemoryEnvelope s addr width
  ```

  bundling:
  - machine mode;
  - MPRV disabled;
  - bare translation;
  - non-device RAM;
  - populated bytes;
  - alignment/no-overflow requirements;
  - no host/advice/panic/termination special region.
- Use that predicate consistently in load/store theorem statements.
- Add tests in Rust that generate states satisfying the envelope and compare
  direct instruction execution with expanded bytecode execution.

This is mostly organization plus proof plumbing. It would make the claims much
clearer and reduce accidental overclaiming.

### 7. Model Advice Tape Behavior

Current issue: Lean models advice as explicit values; Rust `VirtualAdviceLoad`
reads bytes from a mutable FIFO tape.

Path forward:

- Extend `SailJoltState` or a separate execution state with:

  ```lean
  adviceBytes : List UInt8
  adviceCursor : Nat
  ```

- Define `readAdvice n` with little-endian packing and failure on underflow.
- Prove that existing explicit-advice theorems are recovered when the tape
  contains exactly the expected bytes.
- Add width/canonicality lemmas for `ADVICELB/LH/LW/LD`.

This is a clear and fairly self-contained extension. It is especially useful if
the formalization is meant to cover the tracer, not just advice-parametric
instruction semantics.

### 8. Finish Store Proofs Against Current Rust

Current issue: `SB`, `SH`, and parts of `SW` remain incomplete, and stores are
where memory-envelope issues become most painful.

Path forward:

- Start with `SW`, since it is closest to the existing word-store helper work.
- Prove the read-modify-write splice lemma independently:

  ```text
  load aligned dword;
  replace selected word/half/byte;
  store aligned dword
  =
  architectural store of width w
  ```

- Then instantiate for `SW`, `SH`, `SB`.
- Keep misalignment out of scope initially via explicit preconditions, then add
  assertion-failure behavior later.

This is substantial but direct. The proof should become much easier if the
memory envelope and byte/dword splice lemmas are centralized.

### 9. Close Shift Bridge Holes

Current issue: `SLLW` and `SRLW` depend on sorried bridge lemmas around
bitvector arithmetic/bitmask behavior.

Path forward:

- Isolate each bridge lemma in a small math-only file with no monadic state.
- Add exhaustive bounded tests in Rust/Lean for the corresponding 32-bit
  relation to catch statement mistakes.
- Prove the bitvector identities once, then reuse them in both source-level and
  recursive-lowering proofs.

This is pure proof work. It is probably frustrating but not conceptually murky.

### 10. Split Rust Expansion From Tracing

Current issue: bytecode expansion, tracing, CPU execution, advice reads, and
virtual instruction behavior are tightly coupled.

Path forward:

- Extract a pure expansion crate with a small API:

  ```rust
  pub fn expand_instruction(
      instr: DecodedInstruction,
      xlen: Xlen,
      allocator: AllocatorState,
      policy: ExpansionPolicy,
  ) -> Result<ExpandedSequence, ExpansionError>
  ```

- Keep this crate free of:
  - CPU state;
  - memory/MMU;
  - advice tape;
  - host I/O;
  - terminal behavior;
  - trace mutation.
- Make recursive lowering explicit:

  ```rust
  expand_source(instr) -> SourceSequence
  lower_to_primitives(SourceSequence) -> PrimitiveSequence
  annotate_sequence_metadata(PrimitiveSequence) -> ExpandedSequence
  ```

- Put shared definitions in a small base crate only if needed.
- Let the tracer consume `ExpandedSequence` rather than owning expansion logic.

This is the architectural change that would make Hax/Aeneas much more plausible.
The verified surface would be mostly pure functions over enums, lists, small
integers, and allocator state, instead of a tracer entangled with emulator
effects.

### 11. Define the Claim Stack Explicitly

The final proof stack should probably be layered as:

1. Rust expansion determinism:

   ```text
   expand_instruction produces the manifest/final rows claimed.
   ```

2. Recursive lowering correctness:

   ```text
   final primitive rows denote the same behavior as source inline sequence.
   ```

3. Source expansion correctness:

   ```text
   source inline sequence denotes the same architectural behavior as Sail.
   ```

4. Envelope theorem:

   ```text
   under JoltFlatMemoryEnvelope / advice assumptions / rd policy,
   Rust-expanded bytecode is equivalent to Sail for covered instructions.
   ```

The current Lean work is strongest at layer 3 for selected instruction families.
The main missing work is layers 1, 2, and the precise envelope theorem in layer
4.
