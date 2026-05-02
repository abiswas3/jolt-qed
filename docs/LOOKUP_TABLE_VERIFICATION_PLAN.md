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

Bytecode expansion equivalence is not enough. After expansion, Jolt still needs
to prove that every primitive instruction row was executed correctly. The lookup
tables are central to this, because many primitive instruction semantics are
enforced by table membership rather than by directly computing the instruction
result inside the circuit.

The right verification architecture is not "hand-write a Lean model and trust
that it matches Rust", and it is also not "extract the entire lookup-table crate
with Hax/Aeneas". The better plan is hybrid:

```text
Rust materialize_entry/core table functions
  -> small extractable Rust subset, via Hax/Aeneas where possible
  -> Lean entry semantics

Rust evaluate_mle for fixed RV64 tables
  -> symbolic execution
  -> typed polynomial DAG/IR
  -> Lean polynomial definitions

Lean bridge theorem
  -> generated MLE agrees with extracted/materialized table entries on Boolean inputs
```

This keeps the formal artifacts connected to Rust while avoiding the worst parts
of generic Rust extraction: trait-heavy field abstractions, serde/strum
boilerplate, enum dispatch, transcript plumbing, and verifier/prover code that is
not needed for the local table theorem.

The current `zklean-extractor` already demonstrates the most important idea:
symbolically execute Rust `evaluate_mle` at fixed `XLEN = 64` and emit the
resulting polynomial. That is the right center of gravity for `evaluate_mle`.
However, the current emitted Lean is too close to a raw polynomial dump to be the
final architecture. It should be routed through a typed IR and a more robust Lean
code generator.

## Target Formal Claims

The eventual top-level statement should be:

> For every accepted Jolt proof, for every active primitive instruction row in
> the committed trace, the row's constrained instruction output equals the
> semantic result of that primitive instruction applied to the row's constrained
> operands, and that output is the value used by the register, memory, and PC
> transition constraints.

That top-level theorem decomposes into smaller claims. The lookup-table-specific
claim should be:

```text
if row is an active instruction I
and I routes to lookup table T
and row operands produce lookup index idx
and row result is constrained to table value out,
then out = spec_I(row operands)
```

For each lookup table `T`, the local table theorem should have two sides:

```text
materialize_entry_T(idx) = table_spec_T(idx)
```

and:

```text
evaluate_mle_T(bits(idx)) = materialize_entry_T(idx)
```

for Boolean `idx` bitvectors. More generally, once the Boolean theorem is
stable, we can state the full multilinear-extension theorem:

```text
evaluate_mle_T(r)
  = Σ_{b in {0,1}^n} materialize_entry_T(b) * eq(r, b)
```

This scope is intentionally narrower than proving the whole lookup argument at
first. It targets exactly the verifier-facing table functions that are essential
for soundness: `evaluate_mle` and `materialize_entry`.

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
defines a table entry by uninterleaving an index into operands `x` and `y`, then
returning `x & y`.

Instruction-to-table/query implementations live under
[`instructions/`](https://github.com/a16z/jolt/tree/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions).
For example:

- [`instructions/riscv/add.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/riscv/add.rs)
  maps `ADD` through a range-check style table and constrains the wrapped
  addition output.
- [`instructions/virt/assert_mulu_no_overflow.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/virt/assert_mulu_no_overflow.rs)
  maps the multiplication-overflow assertion to the `MulUNoOverflow` table.
- [`instructions/virt/assert_valid_unsigned_remainder.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/virt/assert_valid_unsigned_remainder.rs)
  maps the unsigned remainder check to the `ValidUnsignedRemainder` table.

The table-index convention is implemented in
[`interleave.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/interleave.rs),
where two operands are interleaved into a single lookup index.

The crate already contains useful test scaffolding:

- per-instruction tests in
  [`instructions/test.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/test.rs);
- MLE tests in
  [`tables/test_utils.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/test_utils.rs).

These tests are not formal proofs, but they identify the intended theorem
boundaries.

## Current zkLean Extractor

The existing `zklean-extractor` is important because it already uses the right
basic idea for `evaluate_mle`: run Rust with a symbolic field element, let the
ordinary Rust implementation build an expression DAG, then emit Lean.

In
[`zklean-extractor/src/lookups.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/zklean-extractor/src/lookups.rs),
the extractor builds `2 * XLEN` symbolic variables and calls the real Rust table
method:

```rust
self.lookup_table.evaluate_mle::<F, F>(&reg)
```

In
[`zklean-extractor/src/main.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/zklean-extractor/src/main.rs),
the parameter set is fixed to RV64, so the generated lookup-table polynomials
are specialized to `Vector f 128` in Lean.

This is a good direction. It avoids trying to extract generic field code,
serde/strum derives, table enums, and prover/verifier infrastructure. It also
keeps the generated polynomial connected to the actual Rust `evaluate_mle`
implementation.

However, the current extractor has limitations that should be made explicit.

### Limitation 1: Challenge Representation Is Collapsed

The symbolic field type used by the extractor implements Jolt's field trait with:

```rust
type Challenge = Self;
```

The extraction call also uses the same symbolic type for both generic
parameters:

```rust
evaluate_mle::<F, F>
```

This means the emitted Lean polynomial does not model the production verifier's
challenge type, such as `MontU128Challenge<Fr>`, nor the distribution/embedding
from transcript bytes into field elements. The generated theorem can say
"assuming the challenge coordinates are field elements, this is the polynomial
Rust computes." It cannot by itself say that Jolt's concrete transcript
challenge representation is faithfully modeled.

The fix is not to discard symbolic execution. The fix is to make the symbolic
execution typed:

```text
FieldAst       -- field values
ChallengeAst   -- verifier challenge representation
embed          -- ChallengeAst -> FieldAst, where Rust semantics requires it
```

Then run the Rust formula through something morally like:

```rust
evaluate_mle::<FieldAst, ChallengeAst>
```

and emit Lean that preserves the distinction between sampled challenge
coordinates and field arithmetic.

### Limitation 2: Generated Lean Is Too Verbose

The current Lean output is a large flattened polynomial file. The extractor does
perform common-subexpression elimination, and comments in
[`zklean-extractor/src/mle_ast.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/zklean-extractor/src/mle_ast.rs)
explain that top-level CSE definitions were introduced because large let-bound
expressions were difficult for Lean.

That helps, but it is not enough as a long-term proof artifact. In local
experiments, a generated RV64 lookup-table file was about 2.5 MB and roughly
15k lines, with thousands of top-level helper definitions for only a few dozen
public lookup-table polynomials. Lean spent many minutes and multiple GB of
memory compiling the single generated lookup-table module.

The problem is not symbolic execution itself. The problem is that the current
backend goes directly from Rust AST to final Lean text. We should insert a
stable intermediate representation.

### Limitation 3: Fake Field APIs Hide Extractor Assumptions

The symbolic field implements only the operations the extractor happens to
exercise. Unused field APIs are intentionally left as panics or unimplemented
methods. This is reasonable for a prototype, but it means future Rust changes
can silently move the extractor outside the intended fragment.

The extractor should make the supported fragment explicit and test it:

- which field operations may appear in lookup-table MLE formulas;
- which challenge operations may appear;
- which constants are allowed;
- whether inverses, serialization, transcript methods, or randomness are
  forbidden in lookup-table extraction.

## Recommended Architecture

### 1. Keep Symbolic Execution for `evaluate_mle`

Symbolic execution is the right tool for `evaluate_mle` because Jolt currently
supports fixed RV64 lookup tables. We do not need to extract a general-purpose
evaluator for arbitrary `XLEN`; we need the actual RV64 polynomials the verifier
uses.

The formal artifact should be:

```text
generated_lookup_mle_T : Vector F 128 -> F
```

for each table `T`, with provenance tying it to Rust `evaluate_mle` at a specific
Jolt commit.

### 2. Emit a Typed DAG/IR Before Lean

Instead of emitting Lean directly from the Rust symbolic AST, the extractor
should emit a compact, typed IR:

```text
Table:
  name: And
  xlen: 64
  variables: 128
  nodes:
    n0 = var 0
    n1 = const 1
    n2 = sub n1 n0
    ...
  output: n_k
```

The IR should distinguish:

- field variables;
- challenge variables;
- field constants;
- challenge-to-field embeddings;
- field operations;
- permitted Boolean-style selectors.

This gives us an inspectable and testable artifact between Rust and Lean. It
also lets us improve Lean code generation without rerunning or changing the Rust
symbolic executor.

### 3. Generate Lean in Proof-Friendly Shapes

The Lean backend should be able to choose among several representations:

- one module per table, instead of one huge file;
- balanced expression trees, rather than long left-associated chains;
- shared typed constants for powers of two and common coefficients;
- structured folds/sums for regular bit patterns where possible;
- top-level helper definitions only when they actually reduce elaboration cost;
- stable names that make it clear which Rust table each definition came from.

For human proof work, we should also generate or write a clean specification
next to the extracted polynomial:

```text
spec_And_64_mle
spec_Xor_64_mle
spec_MulUNoOverflow_64_mle
```

and prove:

```text
generated_And_64_mle = spec_And_64_mle
```

or, at minimum:

```text
generated_And_64_mle(bits(idx)) = materialize_entry_And(idx)
```

on Boolean inputs.

### 4. Extract or Hand-Minimize `materialize_entry`

The `materialize_entry` side is different from `evaluate_mle`. It is usually
small bitvector/integer arithmetic, so Hax or Aeneas may work well if we isolate
the core functions.

The Rust crate should expose a small verification-oriented layer with total,
pure functions such as:

```rust
pub enum TableId {
    And,
    Or,
    Xor,
    RangeCheck,
    ValidDiv0,
    ValidUnsignedRemainder,
    MulUNoOverflow,
    // ...
}

pub fn interleave_u64(x: u64, y: u64) -> u128;
pub fn uninterleave_u128(index: u128) -> (u64, u64);
pub fn materialize_entry_u64(table: TableId, index: u128) -> u64;
```

This layer should avoid:

- serde and strum derives;
- macros on the verification path;
- unsafe discriminant tricks;
- trait dispatch;
- tracer dependencies;
- random/test-only code;
- prefix/suffix decomposition;
- prover-only optimizations.

Existing table implementations can delegate to these pure functions, preserving
runtime semantics while giving extraction tools a small target.

### 5. Bridge MLE and Materialization

The first key theorem should be:

```text
generated_mle_T(bits(idx)) = extracted_materialize_entry_T(idx)
```

for all valid Boolean `idx` inputs.

This theorem is the main local soundness claim for each lookup table. It says the
polynomial the verifier evaluates is the multilinear extension of the table
entries that define the intended semantics.

Once this is done, we can prove cleaner semantic theorems:

```text
extracted_materialize_entry_And(interleave(x, y)) = x &&& y
extracted_materialize_entry_Xor(interleave(x, y)) = x ^^^ y
extracted_materialize_entry_MulUNoOverflow(interleave(x, y)) = overflow_guard(x, y)
```

### 6. Model Challenge Representation Separately

We should not erase the distinction between transcript challenges and field
elements. A separate Lean model should capture the verifier's concrete challenge
path:

```text
transcript bytes
  -> MontU128Challenge
  -> field element used in evaluate_mle
```

The theorem should say that when the verifier evaluates the generated polynomial
at embedded challenge coordinates, that evaluation matches the Rust verifier's
challenge interpretation.

This is separate from table-entry correctness, but it is essential for the
soundness claim. It prevents us from accidentally proving a statement about
uniform field variables while the production verifier samples a more structured
challenge representation.

## What To Prove First

### 1. Bit-Indexing Correctness

Prove the bit interleaving convention:

```text
uninterleave(interleave(x, y)) = (x, y)
interleave(uninterleave(idx)) = idx
```

for the relevant RV64-bounded domains.

Relevant Rust:

- [`interleave.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/interleave.rs)
- [`lookup_bits.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/lookup_bits.rs)

### 2. Simple Table Entry Correctness

Start with tables where `materialize_entry` is direct bit arithmetic:

- `And`;
- `Or`;
- `Xor`;
- `Equal`;
- `NotEqual`;
- `RangeCheck`;
- unsigned comparisons.

For each table, prove:

```text
materialize_entry_T(idx) = table_spec_T(idx)
```

### 3. Generated MLE Correctness on Boolean Inputs

For those same tables, prove:

```text
generated_mle_T(bits(idx)) = materialize_entry_T(idx)
```

This is the first place where the symbolic-execution output earns its keep. The
Lean proof should not need to trust a hand-written polynomial.

### 4. Instruction Query and Routing Correctness

For lookup-backed instructions, prove that `LookupQuery` constructs the intended
query and `lookup_table()` selects the intended table.

The existing helper
[`instruction_inputs_match_constraint_test_fn`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/instructions/test.rs)
describes the intended connection between instruction inputs and R1CS flags.

For `AND`, `OR`, `XOR`, `ADD`, and `SUB`, the desired local loop is:

```text
row operands
  -> query index/output
  -> selected table
  -> materialized table entry
  -> primitive instruction semantics
```

### 5. Division and Virtual Guard Tables

Then tackle the tables most relevant to Ari's bytecode-expansion proofs:

- `ValidDiv0`;
- `ValidUnsignedRemainder`;
- `ValidSignedRemainder`;
- `MulUNoOverflow`;
- `VirtualChangeDivisor`;
- `VirtualChangeDivisorW`;
- shift/word-extension tables used by recursively lowered bytecode.

These tables justify the constraints that make the advice-based division and
remainder bytecode sequences sound.

## What Is Not First-Priority

### Prefix/Suffix Decomposition

Jolt contains optimized prefix/suffix decomposition machinery in
[`tables/mod.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/crates/jolt-lookup-tables/src/tables/mod.rs).
That code is important for prover performance and for a fully faithful
implementation proof.

However, it is not the first target for the local soundness theorem. For the
initial lookup-table formalization, we only need:

```text
materialize_entry
evaluate_mle
challenge representation used by the verifier
```

Once those are established, prefix/suffix correctness can be added as an
optimization-refinement theorem:

```text
optimized_prefix_suffix_eval(r) = evaluate_mle(r)
```

### Full Lookup Argument Soundness

The table functions can all be correct while the proof system still fails to
enforce table membership. Eventually we need a theorem about the lookup argument:

```text
if the lookup subprotocol accepts,
then the committed lookup input/output pairs are in the selected tables
```

This reaches beyond the lookup-table crate into the polynomial/proof-system code.
Relevant files include:

- [`jolt-core/src/poly/shared_ra_polys.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/jolt-core/src/poly/shared_ra_polys.rs)
- [`jolt-core/src/poly/rlc_polynomial.rs`](https://github.com/a16z/jolt/blob/d4902c23c210a429b7faafade1570157067f5e2f/jolt-core/src/poly/rlc_polynomial.rs)

This should come after the table-level claims are stable.

### Full zkVM State Transition

Finally, lookup-validated primitive semantics must connect to:

- register reads and writes;
- PC update;
- memory read/write consistency;
- advice/host effects, if in scope.

This is where lookup correctness becomes full zkVM soundness. It is downstream
of the table-level work, not a blocker for starting it.

## Refactoring Recommendations

The Rust lookup-table crate should move toward a small extraction-friendly core
without changing semantics.

### Keep the Current Expressive APIs

The existing trait style is useful for writing formulas. We do not need to remove
operator overloading or generic field traits from production code. The problem is
not that Rust has `Add`/`Mul` traits; Lean can represent heterogeneous operations
perfectly well. The problem is that current extraction tools see too much at
once: associated types, equality constraints, serde derives, macro-generated
impls, const generics, enum metadata, and field/challenge abstractions all mixed
together.

The fix is to expose narrower verification entrypoints, not to make production
code ugly.

### Add a Pure Entry Layer

Add small functions for table materialization and bit-indexing that are:

- total;
- pure;
- macro-light;
- independent of tracer/prover code;
- parameterized only by explicit values such as `TableId` and `u64`/`u128`.

Existing trait implementations should call into these functions. That gives Hax
and Aeneas a simpler target while preserving the current public API.

### Add a Symbolic MLE Backend

Make symbolic extraction an explicit backend rather than an ad hoc printer:

```text
Rust evaluate_mle
  -> typed symbolic AST
  -> canonical DAG/IR
  -> Lean backend
  -> optional JSON/debug artifact
```

The IR should be versioned and include provenance:

- Jolt commit;
- table name;
- `XLEN`;
- Rust function path;
- symbolic field/challenge types used;
- output hash of the DAG.

### Add Buildable Generated Lean Tests

Generated Lean should be checked in CI or in a reproducible script. The script
should fail if:

- generated Lean does not compile;
- a generated table exceeds configured size/time thresholds;
- the extractor uses unsupported symbolic-field operations;
- generated RV64 MLEs fail randomized Rust-side checks against
  `materialize_entry` on Boolean inputs.

## Suggested Milestones

### Milestone A: Stabilize the Claim and Artifacts

Define the exact table-level theorem:

```text
generated_mle_T(bits(idx)) = extracted_materialize_entry_T(idx)
```

for RV64 tables. Decide the first table set: likely `And`, `Or`, `Xor`,
`Equal`, `NotEqual`, and `RangeCheck`.

### Milestone B: Build the Pure Entry Layer

Refactor the lookup crate so simple table entries and bit-indexing live in a
small pure module or crate. Run Hax/Aeneas against this layer only.

### Milestone C: Upgrade Symbolic MLE Extraction

Change the zkLean extractor from direct Lean pretty-printing to:

```text
symbolic AST -> typed DAG/IR -> Lean
```

Also split generated Lean by table and preserve challenge-vs-field distinction
where the Rust verifier does.

### Milestone D: Prove Simple Table Bridges

For the first simple tables, prove:

```text
materialize_entry = table spec
generated_mle(bits(idx)) = materialize_entry(idx)
```

This gives the first real Rust-connected table-correctness theorem.

### Milestone E: Add Challenge Representation

Model the verifier's concrete challenge path and prove that evaluating generated
MLEs at embedded challenges matches the production verifier interpretation.

### Milestone F: Extend to Virtual/Division Guard Tables

Add the tables required to justify bytecode expansion for division, remainder,
overflow, shifts, and recursive lowering.

### Milestone G: Connect to Lookup Argument and State Transition

Only after the local table theorems are stable, prove the protocol-level lookup
argument soundness and connect lookup outputs to register, memory, and PC
transition constraints.

## Relationship To Ari's Current Work

Ari's bytecode-expansion proofs can be viewed as assuming a trusted primitive
instruction semantics. Lookup-table verification is how we discharge that trust
assumption for lookup-backed primitives.

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
