# Jolt Constraints in Lean: Current Model and Roadmap

This document is the onboarding guide for the constraint formalization in
`JoltConstraints/`. Read it before changing that directory.

## End goal

The eventual theorem should say:

> If all Jolt constraints are satisfied, then every trace row must represent an
> instruction stepped correctly according to the existing `JoltISA` semantics.

That is a sufficiency or soundness theorem for the complete Jolt constraint
system. It will require all of the instruction, bytecode, register, memory,
lookup, flag, and consistency constraints.

The current milestone is deliberately smaller. It formalizes one necessary
constraint for `AND`:

> Data produced from an honestly executed final Jolt trace satisfies the AND
> lookup constraint.

Equivalently, if this constraint is violated, the row data could not have come
from a correctly executed final `AND` row. This is necessary but not sufficient:
incorrect or inconsistent prover data may still satisfy this one equation.

## Non-negotiable semantic boundary

`JoltBytecode/JoltISA/` already models the tracer-facing ISA and its execution
semantics. In particular:

- instructions are `JoltISA.Instr`;
- source reads are `JoltISA.readSrc`;
- destination writes are `JoltISA.writeDst`;
- instruction execution is `JoltISA.execInstr`;
- machine states are `SailJoltState`.

Do not define a second execution relation for an instruction. A definition such
as `ANDRowExecutes` that manually sequences reads, computes `&&&`, and performs a
write merely restates the ISA and is not acceptable as the semantic foundation.
The constraint layer must consume the existing monadic `JoltISA` semantics.

The Rust tracer can be consulted to understand Jolt data layout, but it does not
need a second Lean model here. The Lean `JoltISA` layer is the proof boundary.

## The three layers

Keep these layers separate:

1. **Semantic trace.** Instructions and adjacent machine states, with each step
   proved using `JoltISA.execInstr`.
2. **Jolt polynomial data.** Hypercube evaluation arrays filled from a trace or
   claimed by a prover.
3. **Constraints and theorems.** Constraints are stated purely over polynomial
   data and fixed tables; separate theorems relate those constraints to
   execution semantics.

The current AND result goes from layer 1 to layer 2 and proves the layer-3
constraint. Later soundness work will reason in the opposite direction using
the complete collection of constraints.

## Current file layout

- `JoltConstraints/basic.lean`
  - trace-row indexing;
  - `JoltISATrace`;
  - the current final-trace normalization invariant.
- `JoltConstraints/polynomials.lean`
  - committed and virtual polynomial identifiers;
  - dependent evaluation-array storage;
  - `JoltData` and typed accessors.
- `JoltConstraints/and_constraint.lean`
  - the AND table and constraint;
  - the AND-specific honest data projection;
  - the proved necessity theorem.
- `JoltConstraints.lean`
  - the root import.

Keep this base small. Add identifiers and files when another constraint needs
them; do not pre-emptively model the whole protocol.

## Semantic traces

`Column T A` is currently represented as a finite array function:

```lean
abbrev Column (T : Nat) (A : Type) := Fin T → A
```

For polynomial data, these arrays stand for evaluations on Boolean hypercubes.
The protocol may assume that the trace length `T` is a power of two, but the
current AND necessity theorem does not need that fact and does not carry the
assumption yet.

An honest trace is:

```lean
structure JoltISATrace (T : Nat) where
  instr : Column T JoltISA.Instr
  state : Column (T + 1) SailJoltState
  executes : ∀ i : Fin T,
    (JoltISA.execInstr (instr i)).run (state (currentStateIndex i)) =
      .ok RETIRE_SUCCESS (state (nextStateIndex i))
  finalRow : ∀ i : Fin T, FinalTraceRow (instr i)
```

Thus `trace.preState i` and `trace.postState i` are adjacent states, and
`trace.executes i` uses the existing ISA semantics directly.

### Why `finalRow` is needed

Architectural register `x0` is immutable. The ISA can correctly execute
`AND x0, rs1, rs2`, but the computed result is discarded and therefore cannot
be recovered by reading `x0` from the post-state. If the operands AND to a
nonzero value, a theorem equating the post-state destination value with the
lookup-table output would be false.

The real final tracer does not emit such a pure-writeback `AND` row. An
`rd = x0` pure writeback is replaced by an `ADDI x0, x0, 0` no-op row. This
behavior is already represented in `JoltISA.pureWritebackTraceProgram`.

The current partial final-row invariant therefore says:

```lean
def DestinationRecorded : JoltISA.Dst → Prop
  | .vreg _ => True
  | .xreg rd => rd ≠ regidx.Regidx 0

def FinalTraceRow : JoltISA.Instr → Prop
  | .AND dst _ _ => DestinationRecorded dst
  | _ => True
```

This is not an axiom. It is evidence carried by an instance of
`JoltISATrace`, expressing a fact about final tracer rows. Extend
`FinalTraceRow` as future instruction constraints require their own
normalization facts.

## Global Jolt polynomial data

AND uses only a subset of Jolt's committed (sometimes called "real") and
virtual polynomials. The code nevertheless uses a global namespace so future
constraints can share the same data rather than create incompatible
instruction-specific records.

The current identifier hierarchy is:

```lean
inductive JoltCommittedPolynomial where
  | instructionRa

inductive JoltVirtualPolynomial where
  | rdWriteValue
  | lookupTableFlag (table : JoltLookupTable)

inductive JoltPolynomial where
  | committed (id : JoltCommittedPolynomial)
  | virtual (id : JoltVirtualPolynomial)
```

Only identifiers needed by AND are listed at present. Other committed
polynomials are not assumed to have the shape of `instructionRa`.

### Canonical names

Use concise canonical identifiers at call sites:

```lean
JoltPolynomial.instructionRa
JoltPolynomial.rdWriteValue
JoltPolynomial.andFlag
```

Their definitions record the committed/virtual classification once. Avoid
repeating ambiguous relative expressions such as `.committed .instructionRa`
throughout constraints. In constructor pattern matches, where aliases cannot
be used as patterns, qualify at least the outer layer, for example:

```lean
JoltPolynomial.committed .instructionRa
```

### Evaluation shapes

Polynomial data is stored through a dependent type:

```lean
def JoltPolynomial.Evaluations
    (polynomial : JoltPolynomial) (T : Nat) (F : Type) : Type :=
  match polynomial with
  | JoltPolynomial.committed .instructionRa =>
      Column T (InstructionLookupVector F)
  | JoltPolynomial.virtual _ => Column T F

structure JoltPolynomialData (T : Nat) (F : Type) where
  evals : (polynomial : JoltPolynomial) → polynomial.Evaluations T F
```

This design is intentional. `instructionRa` is the `T × 2^128` matrix
`ra(i,k)`, whereas most trace polynomials have one value per row. When adding a
committed polynomial such as `rdInc` or `ramInc`, give that constructor its
actual evaluation shape, typically `Column T F`. If a later polynomial has a
different hypercube domain, encode that domain in its corresponding
`Evaluations` branch. No redesign of `JoltPolynomialData` should be necessary.

### Current AND mapping

| Specification name | Canonical identifier | Kind | Evaluation storage |
|---|---|---|---|
| `AND_FLAG` | `JoltPolynomial.andFlag` | virtual | `Column T F` |
| `RD_val` | `JoltPolynomial.rdWriteValue` | virtual | `Column T F` |
| `ra` | `JoltPolynomial.instructionRa` | committed | `Column T (InstructionLookupKey → F)` |
| `trace` | not a field polynomial | semantic metadata | `Column T JoltISA.Instr` |
| `T_AND` | not witness data | fixed lookup table | `InstructionLookupKey → F` |

`JoltData` contains the semantic instruction metadata and the global named
polynomial store. Specification-facing accessors retain the readable names
`data.AND_FLAG`, `data.RD_val`, and `data.ra`.

## The AND lookup table

The key space is represented as a pair of 64-bit finite operands:

```lean
abbrev InstructionLookupOperand := Fin (2 ^ 64)
abbrev InstructionLookupKey :=
  InstructionLookupOperand × InstructionLookupOperand
```

This is equivalent to a 128-bit concatenated key and avoids unnecessary bit
slicing in the current proof.

The concrete table value is:

```lean
def ANDTableValue (key : ANDLookupKey) : BitVec 64 :=
  BitVec.ofFin key.1 &&& BitVec.ofFin key.2
```

For a field `F`, `encodedANDTable encode` applies the same encoding
`BitVec 64 → F` to every table output.

## The constraint

For every trace row `i`, the specification requires:

\[
AND\_FLAG[i]
\left(
  RD\_val[i] - \sum_{k \in \{0,1\}^{128}} ra(i,k)T_{AND}(k)
\right)=0.
\]

The Lean definition is stated only in terms of prover-facing `JoltData` and the
fixed table:

```lean
def ANDConstraint {T : Nat} {F : Type} [Field F]
    (data : JoltData T F) (T_AND : ANDTable F) : Prop :=
  ∀ i : Fin T,
    data.AND_FLAG i *
      (data.RD_val i -
        ∑ k : ANDLookupKey, data.ra i k * T_AND k) = 0
```

There are no machine states or ISA execution relations in this definition.
That separation is essential: a Jolt constraint must be checkable from the
claimed polynomial data.

## Honest projection for the AND milestone

`JoltISATrace.toANDData` produces the currently modelled polynomial data from
an honest semantic trace:

- `trace` is copied from `JoltISATrace.instr`;
- on an AND row, `AND_FLAG` is one;
- `RD_val` is encoded from the destination in the post-state;
- the two source values are read from the pre-state using `JoltISA.readSrc`;
- `ra(i,·)` is one-hot at the pair of source values;
- for a non-AND row, this AND-specific projection uses zero for these entries.

The function returns global `JoltData`, but it is intentionally only the
projection needed for the present AND theorem. As more instructions are added,
the tracer-to-polynomial construction should be consolidated so shared
polynomials such as `rdWriteValue` contain the correct value on every relevant
instruction row.

Small `[simp]` projection lemmas expose the values of `AND_FLAG`, `RD_val`, and
`ra`. Do not unfold the entire dependent polynomial store in proofs; doing so
is slow and will become worse as more polynomial identifiers are added.

## The main theorem

The proved theorem is:

```lean
theorem ANDConstraint_isNecessary
    {T : Nat} {F : Type u} [Field F]
    (trace : JoltISATrace T)
    (encode : BitVec Xlen → F) :
    ANDConstraint
      (trace.toANDData encode)
      (encodedANDTable encode)
```

In English:

> Take a final trace whose rows execute according to `JoltISA.execInstr`. Fill
> the AND-related Jolt polynomial evaluations from that trace. Those
> evaluations satisfy the specified AND lookup constraint at every row.

For non-AND rows, the flag is zero and the equation is immediate. For an AND
row, the proof uses the existing `JoltISA.execInstr (.AND ...)` computation to
show that the destination read from the post-state equals the bitwise AND of
the two sources read from the pre-state. The one-hot sum then reduces to the
selected entry in `T_AND`.

There are no `sorry` declarations or axioms in `JoltConstraints/`.

### What is assumed about AND positions

For this necessity theorem, the honest instruction trace is an input. If
`trace.instr i` is `AND`, `trace.executes i` proves that it was executed
correctly. `toANDData` derives `AND_FLAG[i] = 1` from that instruction.

The current AND equation does **not** prove, for arbitrary prover data, that

```text
AND_FLAG[i] = 1  ⇒  trace[i] is actually AND.
```

That selector-to-bytecode correspondence is assumed by the honest projection
for now. A later bytecode/selector constraint must enforce it in the soundness
direction. Booleanity of flags and the correctness/one-hot structure of claimed
lookup addresses likewise belong to the wider constraint system.

### Why `encode` need not be injective yet

The necessity direction only transports a concrete word equality through the
same function `encode`. Therefore the theorem is valid for any
`encode : BitVec 64 → F`.

The reverse, sufficiency direction will need an appropriate encoding contract,
such as injectivity on the represented word range or a canonical field
embedding with range constraints. Do not add that requirement to the current
necessity theorem.

## What is not proved

The current result does not show any of the following:

- arbitrary `AND_FLAG` claims agree with bytecode;
- `AND_FLAG` is Boolean;
- arbitrary `ra` rows are one-hot or select the actual source values;
- arbitrary `RD_val` agrees with the register write polynomial;
- satisfying the AND equation implies that an AND instruction executed
  correctly;
- every non-AND instruction executes correctly;
- the complete Jolt constraint system is sound.

Those are future constraints and composition theorems. Do not claim
sufficiency from `ANDConstraint_isNecessary`.

## Expected next steps

Proceed incrementally:

1. Add the next required committed or virtual polynomial identifier to the
   global inductive namespace.
2. Give it its correct dependent evaluation shape and a canonical
   `JoltPolynomial.*` name.
3. Add a typed `JoltData` accessor.
4. Extend the honest trace-to-data construction without duplicating ISA
   semantics.
5. State the next constraint purely over `JoltData` and fixed tables.
6. Prove its necessity using `JoltISA.execInstr`.
7. Add bytecode, selector, Booleanity, register, lookup-address, and other
   consistency constraints needed for eventual sufficiency.
8. Only after the required family is present, state the global theorem that all
   constraints force every row to step correctly.

## Rules for future agents

- Preserve `JoltISA.execInstr` as the single instruction execution semantics.
- Do not introduce custom per-instruction execution predicates that restate the
  monadic ISA program.
- Constraints themselves must mention only Jolt data and fixed public tables,
  not `SailJoltState`.
- Keep the semantic trace, polynomial data, and constraint layers distinct.
- Treat `AND_FLAG`, `RD_val`, and `ra` as views of global named polynomials, not
  independent permanent storage fields.
- Do not assume every committed polynomial has the matrix shape of
  `instructionRa`; extend `JoltPolynomial.Evaluations` per constructor.
- Prefer canonical identifiers such as `JoltPolynomial.instructionRa` at use
  sites. Fully qualify the outer constructor in pattern matches.
- Do not hide the `x0` issue. A post-state cannot reveal a discarded write;
  final-tracer normalization is required.
- Do not add an axiom for tracer correctness.
- Do not add a separate contrapositive theorem unless it becomes useful; it is
  logically immediate from necessity.
- Keep the model small and build after every structural change.

## Build and validation

Run:

```bash
lake build JoltConstraints
lake build
rg -n '\bsorry\b|\baxiom\b' JoltConstraints JoltConstraints.lean
```

At the time of this rewrite, both builds pass and the final search is empty.
The full repository has pre-existing `sorry` warnings outside
`JoltConstraints/`; they are unrelated to this milestone.
