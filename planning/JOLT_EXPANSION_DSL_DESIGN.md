# A Minimal Recipe Language for Jolt Bytecode Expansion

This note sketches a paper-level account of bytecode expansion as a small
domain-specific language. The purpose of the language is to give a canonical
mathematical object that can be implemented directly in Rust and formalized
directly in Lean, without making either implementation the source of truth for
the other.

## Motivation

The Jolt prover consumes an expanded bytecode program rather than the original
RISC-V program. Many RV64 instructions are not represented by a single target
row in the prover-facing bytecode. Instead, they are lowered into finite
sequences of Jolt bytecode rows, possibly using temporary virtual registers and
possibly invoking the lowering of helper instructions.

The central verification problem is therefore not merely to show that a
hand-written sequence of Jolt instructions simulates a corresponding Sail
RISC-V instruction. It is to connect four objects:

```text
RV64 source instruction
  -> expansion recipe
  -> materialized Jolt bytecode rows
  -> Jolt/Sail semantic execution
```

The expansion recipe is the intended common interface between implementation
and proof. It is deliberately small: it records the structural operations used
by bytecode expansion, but it does not model proof constraints, lookup tables,
trace generation, or the Sail ISA.

## Abstract Syntax

Let `Kind` range over Jolt instruction kinds, including both source-only
instructions and final target-legal Jolt bytecode instructions. Let `Reg` range
over concrete architectural and virtual registers, and let `Tmp` range over
symbolic temporary names local to a recipe.

Operands are either concrete registers or recipe-local temporaries:

```text
Operand ::= reg(Reg) | tmp(Tmp)
```

A row template is an instruction kind together with optional destination and
source operands and an immediate:

```text
RowTemplate ::= row(
  kind : Kind,
  rd   : Option Operand,
  rs1  : Option Operand,
  rs2  : Option Operand,
  imm  : Integer
)
```

The expansion language consists of four operations:

```text
Op ::=
  | emit(RowTemplate)
  | expand(RowTemplate)
  | alloc(Tmp)
  | free(Tmp)

Recipe ::= List Op
```

The distinction between `emit` and `expand` is semantic. An `emit` operation
asserts that the row template is already target-legal and should appear in the
final expanded bytecode after resolving operands. An `expand` operation asserts
that the row template denotes a helper source instruction whose own expansion
must be recursively materialized before appending rows to the enclosing
sequence.

## Materialization Semantics

Materialization interprets a recipe relative to a source instruction, an
allocator state, and an expansion relation for helper rows. It either fails or
returns a finite list of final bytecode rows and an updated allocator state.

Informally:

```text
materialize(source, recipe, allocator) =
  run recipe left-to-right with local temp environment env
```

The local environment maps symbolic temporaries to concrete virtual registers:

```text
Env : Tmp -> Option Reg
```

The operations have the following intended semantics.

`alloc(t)` allocates a concrete temporary virtual register from the instruction
temporary register pool and binds it to `t`. It fails if `t` is already bound or
if the pool is exhausted.

`free(t)` releases the concrete register bound to `t` and removes the binding.
It fails if `t` is unbound.

`emit(template)` resolves all concrete and temporary operands in `template`,
checks that the resulting instruction kind is target-legal, sets the row address
to the source instruction address, and appends the resulting row to the output
buffer.

`expand(template)` resolves the template into a source row at the source
instruction address, recursively expands that row with the same allocator, and
appends the resulting final rows to the output buffer. Recursive expansion is
therefore part of the semantics of the recipe language, not an incidental
implementation detail.

After all operations have executed, materialization fails if any recipe-local
temporary remains live. Otherwise the output rows are stamped with source-level
metadata:

```text
is_first_in_sequence(row_i)        = (i = 0)
virtual_sequence_remaining(row_i) = n - i - 1
is_compressed(row_i)              = source.is_compressed && (i = n - 1)
```

where `n` is the number of materialized rows. Thus the metadata is derived from
the entire expansion of the source instruction, including recursively expanded
helper rows.

## Well-Formedness

A recipe is well-formed for a source instruction if materialization succeeds.
Equivalently, it satisfies the operational side conditions enforced by
materialization:

1. Every temporary use is dominated by a matching allocation.
2. No temporary is allocated twice while live.
3. Every allocated temporary is eventually freed.
4. Every `emit` operation produces a target-legal row.
5. Every `expand` operation denotes a source instruction for which recursive
   expansion is defined.
6. The final output sequence is non-empty and within the metadata capacity
   bound.

These conditions are intentionally dynamic in the implementation and can be
stated as predicates in the formal model. For proof engineering, many concrete
recipes can discharge well-formedness by computation.

## Relation to `JoltISA`

The `JoltISA` layer gives a semantic target for final bytecode rows. It defines
typed Jolt bytecode instructions and an interpreter over `SailJoltState`.
The recipe language is one level above `JoltISA`: it describes how source
instructions are compiled into final rows. A row translation function connects
the two:

```text
translateRow : NormalizedInstruction -> Option JoltISA.Instr
```

For a materialized sequence `rows`, successful translation yields a
straight-line `JoltISA.Program`:

```text
translateRows(rows) = JoltISA.Program.seq (map translateRow rows)
```

Instructions with early-return behavior, such as alignment assertions and
loads, are handled by the existing `JoltISA.Program` semantics: execution
continues only after `RETIRE_SUCCESS`; non-retire results stop the program.

## Correctness Statements

The desired theorem for a single instruction family has three layers.

First, recipe materialization is defined:

```text
expandRecipe(I) = R
materialize(I, R, A0) = (rows, A1)
translateRows(rows) = P
```

Second, the materialized program implements the intended Jolt-level semantic
decomposition:

```text
execProgram(P, js) = execJoltDecomposition(I, js)
```

Third, the Jolt-level decomposition refines the Sail instruction semantics
under the usual architectural and memory assumptions:

```text
projectResult(execJoltDecomposition(I, js))
  = executeSailInstruction(I, js.sail)
```

Combining these gives the bytecode expansion theorem:

```text
projectResult(execProgram(translateRows(materialize(expandRecipe(I))), js))
  = executeSailInstruction(I, js.sail)
```

The projection hides auxiliary virtual-register state while preserving the
architectural state and execution result.

## Implementation Discipline

Rust and Lean should both implement the recipe language natively.

In Rust, the existing `ExpansionBuilder` API is already a direct embedding of
the recipe language:

```text
allocate, emit_*, expand_*, release, finalize
```

In Lean, the recipe language should be represented by inductive datatypes for
operands, row templates, operations, and recipes, together with an executable
materializer. Per-instruction recipes should be ordinary Lean definitions rather
than generated proof artifacts.

The two implementations should be kept synchronized by small manifests or
tests, but the conceptual source of truth is the paper-level recipe language
and its semantics. Generated JSON fixtures are useful for regression testing;
they are not the formal object being verified.

## Register Allocation Interface

The language treats temporary names symbolically. The materializer is
responsible for assigning them to concrete virtual registers.

The intended Jolt partition is:

```text
x0..x31      architectural registers
v32..v39     reserved virtual registers
v40..v47     instruction-local temporary registers
v48..v127    inline-provider temporary registers
```

Provider-free bytecode expansion uses only the instruction-local temporary
pool. Registered inline expansion is intentionally outside this minimal recipe
language unless and until inline recipes are given the same first-order shape.

This split is important for the proof statement: recipe-local temporaries may
be alpha-renamed at the symbolic level, but after materialization they occupy a
specific concrete register pool disjoint from architectural registers, reserved
virtual registers, and inline-provider temporaries.

## Scope and Non-Scope

The recipe language specifies bytecode expansion only. It does not specify:

- the RV64 decoder;
- Sail instruction semantics;
- lookup-table semantics;
- trace witness generation;
- polynomial constraints;
- registered inline implementations.

Those components should be connected by separate refinement theorems or
implementation checks. Keeping the recipe language this small is the main
reason it is suitable as a shared formal object between the paper, Rust, and
Lean.

