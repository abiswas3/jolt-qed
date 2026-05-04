# Plan: Virtual Register Renaming

This note records known proof debt around virtual-register names.

## Issue

Lean proofs often use fixed virtual-register names such as:

```text
v0, v1, v2, ...
```

Rust uses a virtual-register allocator. The exact allocated numbers can depend
on the allocator state, reserved registers, inline temporaries, and nested
expansion.

For many semantic proofs this is harmless because the fixed Lean names are just
a canonical template. But the connection to Rust is not fully explicit unless we
prove that allocator-chosen names are equivalent to the fixed template names.

## Current Position

This is known laziness in the model, and we are intentionally not addressing it
now.

The informal assumption is:

```text
the Lean virtual registers are fresh and disjoint in the same way the Rust
allocator's registers are fresh and disjoint
```

Under that assumption, the fixed-name proof represents the Rust-allocated
program up to renaming.

## Later Work

The preferred fix is a renaming-invariance theorem.

Sketch:

```text
if rho is injective on every virtual register touched by program p,
then running rename(rho, p) is equivalent to running p under renamed vregs.
```

Then each fixed Lean expansion can be treated as a canonical template, and the
Rust allocator output is connected by choosing an injective renaming from the
template registers to the allocated registers.

Alternative:

```text
parameterize every Lean expansion over allocator outputs
```

That is more direct but likely makes the proofs noisier. Renaming invariance is
probably the better long-term path.

