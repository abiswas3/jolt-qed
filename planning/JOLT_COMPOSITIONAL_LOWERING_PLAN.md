# Plan: Compositional Lowering Theorems

This note records the simpler recursive-expansion issue and the intended proof
strategy.

## Core Point

Rust inline expansion is recursive:

```rust
self.sequence.extend(inst.inline_sequence(&self.allocator, self.xlen));
```

So when a source expansion emits an instruction such as `SLLI`, `SLL`, `SRAI`,
or `SRL`, Rust appends that instruction's own inline sequence, not necessarily
the instruction itself.

This does not mean caller proofs should expand everything from scratch.

The intended proof architecture is compositional:

```text
final rows for sub-instruction = semantic sub-instruction
caller source sequence using semantic sub-instructions = Sail instruction
therefore final recursively expanded caller sequence = Sail instruction
```

## What We Should Not Do

Do not duplicate recursive expansion inside every caller proof.

For example, an `LB` proof should not manually expand every internal `SLLI`,
`SLL`, and `SRAI` into final virtual rows. That would create brittle,
duplicated proofs.

Instead, prove the lowering of each recursively expanding instruction once, then
reuse those theorems by transitivity.

## Required Theorem Shape

The important detail is that lowering theorems must match the register mode in
which callers use the instruction.

For example, architectural `SLLI` has a real-register theorem:

```text
Jolt expansion of architectural SLLI rd, rs1, shamt
=
Sail architectural SLLI rd, rs1, shamt
```

But a load expansion may use:

```text
SLLI v0, v0, 3
```

which is virtual-register to virtual-register. That needs a matching variant:

```text
VirtualMULI vd, vs1, 2^shamt
=
vreg_SLLI vd vs1 shamt
```

Likewise, boundary cases need boundary variants:

```text
VirtualSRAI rd, vs1, bitmask(shamt)
=
vreg_SRAI_to_real rd vs1 shamt
```

## Initial Lowering Families

The first useful set of lowering theorems should cover the recursively lowered
shift instructions used inside loads/stores and advice sequences:

```text
SLLI  -> VirtualMULI
SLL   -> VirtualPow2; MUL
SRLI  -> VirtualSRLI with computed bitmask
SRL   -> VirtualShiftRightBitmask; VirtualSRL
SRAI  -> VirtualSRAI with computed bitmask
SRA   -> VirtualShiftRightBitmask; VirtualSRA
```

Word variants should be handled similarly:

```text
SLLIW
SLLW
SRLIW
SRLW
SRAIW
SRAW
```

Some of these already have architectural real-register theorems. The remaining
work is to add virtual-register and real/virtual boundary variants where caller
expansions need them.

## Example: LB

The RV64 source expansion for architectural `LB` contains:

```text
SLLI v0, v0, 3
SLL  v1, v1, v0
SRAI rd, v1, 56
```

The final Rust rows contain lower-level virtual instructions instead.

The desired proof stack is:

```text
VirtualMULI v0, v0, 8
= vreg_SLLI v0 v0 3

VirtualPow2 tmp, v0; MUL v1, v1, tmp
= vreg_SLL v1 v1 v0

VirtualSRAI rd, v1, bitmask(56)
= vreg_SRAI_to_real rd v1 56

semantic LB source sequence
= Sail LB
```

Therefore the final recursively expanded Rust `LB` sequence matches Sail,
without expanding all of `LB` manually.

## Practical Milestones

1. Inventory instructions whose Rust `inline_sequence` returns more than
   themselves.
2. For each such instruction, record:
   - Rust source inline sequence
   - final recursively expanded sequence
   - Lean semantic helper
   - theorem variants already present
   - missing virtual/boundary theorem variants
3. Add lowering theorems for the missing variants.
4. Keep caller proofs at the semantic source-sequence level.
5. Add small transitivity lemmas only where useful, rather than unfolding every
   caller expansion.

## Claim After This Work

Once the needed lowering variants exist, semantic source-sequence proofs are not
less faithful than final-row proofs. They are faithful compositionally:

```text
final recursive rows
= semantic source sequence
= Sail architectural semantics
```

