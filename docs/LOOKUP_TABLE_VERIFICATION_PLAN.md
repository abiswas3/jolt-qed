# Plan: Formal Verification of Jolt Lookup Tables

This note expands the verification scope beyond bytecode expansion. Ari's current
Lean work mostly addresses whether Jolt bytecode expansions have the intended
architectural meaning. The next layer is to verify that Jolt's proving system
actually enforces the semantics of the primitive instructions appearing in those
expanded bytecode rows.

All Jolt code links below point to the public `a16z/jolt` repository, pinned to
commit
[`d4902c23c210a429b7faafade1570157067f5e2f`](https://github.com/a16z/jolt/tree/d4902c23c210a429b7faafade1570157067f5e2f).

## Executive Summary

The high-level instinct is correct: bytecode expansion equivalence is not enough.
After expansion, Jolt still needs to prove that every primitive instruction row
was executed correctly. The lookup tables are central to this, because many
primitive instruction semantics are enforced by table membership rather than by
directly computing the instruction result inside the circuit.

However, "prove the lookup tables are correct" is only one piece of the real
claim. The full primitive-instruction story needs to connect:

```text
trace row operands
  -> lookup query/index
  -> selected lookup table
  -> table output
  -> instruction result
  -> register/memory/PC transition constraints
```

The new `crates/jolt-lookup-tables` crate is a promising verification target. It
already separates much of the lookup-table logic into small, mostly pure
functions. But it should be made even more verification-oriented before trying to
extract it wholesale with Hax or Aeneas.

## The Formal Claim

The target theorem should be explicit and layered. A good top-level statement is:

> For every accepted Jolt proof, for every active primitive instruction row in
> the committed trace, the row's constrained instruction output equals the
> semantic result of that primitive instruction applied to the row's constrained
> operands, and that output is the value used by the register, memory, and PC
> transition constraints.

This theorem has intentional caveats:

- memory loads/stores also depend on RAM/read-write consistency arguments;
- branches and jumps affect PC rather than ordinary `rd` writeback;
- advice and host I/O require separately modeled external inputs;
- some system/trap behavior may be outside the initial semantic envelope;
- instructions with `lookup_table() = None` must be handled by other constraint
  families.

For lookup-backed instructions, the core local claim should be:

```text
if row is an active instruction I
and I routes to lookup table T
and row operands produce lookup index idx
and row result is constrained to table value out,
then out = spec_I(row operands)
```

## Relevant Rust Structure

The lookup crate exposes three core traits in
[`traits.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/traits.rs):

- `LookupTable`, with `materialize_entry` and `evaluate_mle`;
- `InstructionLookupTable`, mapping an instruction to its table;
- `LookupQuery`, mapping a concrete cycle to instruction inputs, lookup index,
  and lookup output.

The closed table universe is represented by `LookupTableKind` in
[`tables/mod.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/mod.rs).

Individual tables are usually small and mathematical. For example, the `AND`
table in
[`tables/and.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/and.rs)
defines:

```text
materialize_entry(index) = x & y
```

where `x` and `y` are recovered from the interleaved lookup index.

Instruction-to-table/query implementations live under
[`instructions/`](https://github.com/a16z/jolt/tree/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions).
For example:

- [`instructions/riscv/add.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/riscv/add.rs)
  maps `ADD` to `RangeCheck` and uses the wrapped addition as the lookup
  output.
- [`instructions/virt/assert_mulu_no_overflow.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/virt/assert_mulu_no_overflow.rs)
  maps the multiplication-overflow assertion to the `MulUNoOverflow` table.
- [`instructions/virt/assert_valid_unsigned_remainder.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/virt/assert_valid_unsigned_remainder.rs)
  maps the unsigned remainder check to the `ValidUnsignedRemainder` table.

The table-index convention is implemented in
[`interleave.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/interleave.rs),
where two operands are interleaved into a single lookup index.

The crate already contains strong test scaffolding:

- per-instruction tests in
  [`instructions/test.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/test.rs);
- MLE and prefix/suffix tests in
  [`tables/test_utils.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/test_utils.rs).

These tests are not formal proofs, but they are a useful map of the intended
theorem boundaries.

## What Needs To Be Proved

### 1. Bit-Indexing Correctness

Prove that the bit interleaving convention is correct:

```text
uninterleave_bits(interleave_bits(x, y)) = (x, y)
interleave_bits(uninterleave_bits(idx)) = idx
```

for the relevant `XLEN`-bounded domains.

This is foundational because most two-operand tables interpret the lookup index
by uninterleaving its bits.

Relevant Rust:

- [`interleave.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/interleave.rs)
- [`lookup_bits.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/lookup_bits.rs)

### 2. Table Entry Correctness

For every lookup table `T`, prove that:

```text
T.materialize_entry(idx) = spec_T(idx)
```

Examples:

- `AndTable`: output is `x & y`.
- `XorTable`: output is `x ^ y`.
- `RangeCheckTable`: output says whether a combined value is in range.
- `ValidDiv0Table`: output encodes the division-by-zero guard.
- `ValidUnsignedRemainderTable`: output encodes
  `divisor = 0 || remainder < divisor`.
- `VirtualChangeDivisorTable`: output encodes the signed division overflow
  divisor adjustment.

This is the most direct table-correctness theorem. It is mostly bitvector and
integer arithmetic.

### 3. MLE Correctness

For every lookup table `T`, prove that `evaluate_mle` is the multilinear
extension of `materialize_entry`:

```text
evaluate_mle_T(bits(idx)) = materialize_entry_T(idx)
```

for all Boolean `idx` bitvectors, and more generally:

```text
evaluate_mle_T(r)
  = Σ_{b in {0,1}^n} materialize_entry_T(b) * eq(r, b)
```

The tests in
[`tables/test_utils.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/test_utils.rs)
already check this on the Boolean hypercube for small `XLEN`; the proof should
turn that test shape into a theorem.

### 4. Prefix/Suffix Decomposition Correctness

Jolt does not always use a naive full-table MLE evaluation. Tables implement
`PrefixSuffixDecomposition`, with:

```text
table_mle(r) = Σ_i prefix_i(r_high) * suffix_i(r_low)
```

This is represented by `suffixes` and `combine` in
[`tables/mod.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/mod.rs).

For each table, prove:

```text
combine(prefix_evals, suffix_evals) = evaluate_mle(r)
```

This layer matters for prover/verifier correctness because optimized
prefix/suffix evaluation is what the protocol actually uses.

### 5. Instruction Query Correctness

For every lookup-backed instruction, prove that `LookupQuery` extracts the
right operands and constructs the right lookup index.

This has two parts:

1. `to_instruction_inputs` agrees with the instruction-input columns reconstructed
   by the R1CS flags.
2. `to_lookup_index` and `to_lookup_output` agree with the intended instruction
   semantics.

The existing test helper
[`instruction_inputs_match_constraint_test_fn`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/test.rs)
already describes the intended connection to the instruction-input R1CS
constraint.

### 6. Instruction Routing Correctness

For every instruction, prove that `lookup_table()` selects the right table.

This sounds mundane, but it is security-critical: a perfect table does not help
if an instruction is routed to the wrong table.

Relevant Rust:

- [`InstructionLookupTable` in `traits.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/traits.rs)
- instruction metadata in
  [`crates/jolt-riscv/src/instructions/mod.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-riscv/src/instructions/mod.rs)

### 7. Lookup Argument Soundness

The table functions can all be correct while the proof system still fails to
enforce table membership. We also need a theorem about the lookup argument:

```text
if the lookup subprotocol accepts,
then the committed lookup input/output pairs are in the selected tables
```

This reaches beyond the lookup-table crate into the polynomial/proof-system code.
Relevant files include:

- [`jolt-core/src/poly/shared_ra_polys.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/jolt-core/src/poly/shared_ra_polys.rs)
- [`jolt-core/src/poly/rlc_polynomial.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/jolt-core/src/poly/rlc_polynomial.rs)

This is likely a later-stage theorem. It is more about the Shout/Twist lookup
argument than about individual instruction semantics.

### 8. State-Transition Connection

Finally, prove that the table output is actually the value consumed by the
machine transition constraints:

```text
lookup output = instruction result column
instruction result column = value written to rd / PC / memory effect
```

This is where lookup correctness connects to full zkVM soundness. It involves
instruction flags, register read/write constraints, memory read/write arguments,
and PC transition constraints.

## Suggested Milestones

### Milestone A: Pure Lookup Table Spec in Lean

Define a Lean namespace with:

- `TableId`;
- `InstrId`;
- `interleave` / `uninterleave`;
- `tableEntry : TableId -> BitVec (2 * XLEN) -> BitVec XLEN`;
- `instrLookupQuery : PrimitiveRow -> Option (TableId × Index × Output)`;
- simple instruction specs for `AND`, `OR`, `XOR`, `ADD`, `SUB`, `SLT`, etc.

Do not model polynomial commitments or sumcheck yet.

### Milestone B: Prove Simple Tables

Start with the easiest tables:

- `And`;
- `Or`;
- `Xor`;
- `Equal`;
- `NotEqual`;
- `RangeCheck`;
- unsigned comparisons.

For each table:

1. prove `materialize_entry = spec`;
2. prove `evaluate_mle` agrees with `materialize_entry` on Boolean points;
3. prove prefix/suffix `combine` agrees with `evaluate_mle`.

### Milestone C: Prove Query Correctness for Simple Instructions

For `AND`, `OR`, `XOR`, `ADD`, `SUB`, prove:

```text
LookupQuery.to_lookup_output(row) = primitiveInstrSpec(row)
LookupTable.materialize_entry(to_lookup_index(row)) = to_lookup_output(row)
```

This is the first complete local loop:

```text
row operands -> query -> table -> output -> primitive semantics
```

### Milestone D: Prove Virtual/Division Guard Tables

Then tackle the tables most relevant to Ari's bytecode-expansion proofs:

- `ValidDiv0`;
- `ValidUnsignedRemainder`;
- `ValidSignedRemainder`;
- `MulUNoOverflow`;
- `VirtualChangeDivisor`;
- `VirtualChangeDivisorW`;
- shift/bitmask-related virtual tables.

These tables justify the constraints that make the advice-based division and
remainder bytecode sequences sound.

### Milestone E: Connect To Lookup Argument

Prove the polynomial/protocol-level statement:

```text
accepted lookup argument
  -> every active lookup row is consistent with its selected table
```

This should be done after the table specs are stable, since it is a larger proof
about the lookup protocol rather than the tables themselves.

### Milestone F: Connect To zkVM State Transition

Finally, prove that lookup-validated primitive semantics are connected to the
state transition constraints for:

- register reads and writes;
- PC update;
- memory read/write consistency;
- advice/host effects, if in scope.

This is the point where we can claim a meaningful end-to-end primitive
instruction soundness theorem.

## Hax/Aeneas Extraction Assessment

The lookup-table crate is a much better extraction target than the tracer. It is
mostly pure and has small mathematical functions. But I would not try to extract
the entire crate as-is.

### What Looks Extraction-Friendly

- Small table marker structs.
- Pure `materialize_entry` functions.
- Mostly deterministic bitvector arithmetic.
- A finite `LookupTableKind` enum.
- Clear separation between table entries and instruction queries.

### What Will Likely Need Refactoring

- Heavy trait/generic style around `Field`, `ChallengeOps`, and `FieldOps`.
- Const generics over `XLEN`.
- Macros such as `impl_lookup_table!`.
- Serde/derive/strum boilerplate mixed into verified types.
- The `unsafe` discriminant trick in `LookupTableKind::index`.
- `debug_assert` preconditions rather than explicit total APIs.
- Dependencies on `jolt-trace` and `tracer` for query/test interop.
- Optimized bit hacks over `u128`, which may be harder for extraction tools than
  simple structural bitvector definitions.

### Recommended Verification-Oriented Rust Core

Create a small pure core, either as a new crate or a verification-only module:

```rust
pub enum XLen { X8, X32, X64 }
pub enum TableId { And, Or, Xor, RangeCheck, ValidDiv0, ... }
pub enum PrimitiveInstr { Add, And, Xor, AssertValidDiv0, ... }

pub struct PrimitiveRow {
    instr: PrimitiveInstr,
    rs1: u64,
    rs2: u64,
    imm: i128,
    pc: u64,
}

pub fn interleave(x: u64, y: u64, xlen: XLen) -> u128;
pub fn table_entry(table: TableId, xlen: XLen, index: u128) -> u64;
pub fn lookup_query(row: PrimitiveRow, xlen: XLen)
    -> Option<(TableId, u128, u64)>;
pub fn primitive_spec(row: PrimitiveRow, xlen: XLen) -> PrimitiveEffect;
```

This core should avoid:

- macros;
- trait dispatch;
- serde;
- unsafe;
- random/test-only code;
- field-generic MLE code at first;
- tracer/emulator dependencies.

Then prove:

```text
lookup_query(row) = Some(table, idx, out)
  -> table_entry(table, idx) = out
  -> out agrees with primitive_spec(row)
```

After that, add MLE and prefix/suffix layers.

## Relationship To Ari's Current Work

Ari's current bytecode-expansion proofs can be viewed as assuming a trusted
primitive-instruction semantics. Lookup-table verification is how we discharge
that trust assumption for lookup-backed primitives.

For the division/remainder advice family, the most relevant next tables are:

- `ValidDiv0`;
- `ValidUnsignedRemainder`;
- `MulUNoOverflow`;
- `VirtualChangeDivisor`;
- `VirtualChangeDivisorW`;
- shift/word-extension tables used by recursively lowered bytecode.

Once those are proved, the story becomes much stronger:

```text
Sail instruction
  = source bytecode expansion semantics
  = final primitive bytecode semantics
  = lookup/R1CS-enforced primitive semantics
```

That is the route from "the bytecode expansion is mathematically right" to "the
Jolt proof system actually enforces the right computation."
