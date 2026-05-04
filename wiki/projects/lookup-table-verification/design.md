# Lookup Table Verification Design

![Type](https://img.shields.io/badge/type-design_note-24292f)
![Project](https://img.shields.io/badge/project-lookup_tables-yellow)

## Problem

The verifier checks table consistency using polynomial evaluations. The public
table is conceptually large, so the verifier evaluates its multilinear
extension directly instead of materializing every entry.

The first target is the AND table.

> [!TIP]
> Keep the first theorem about the concrete Rust table code:
> `materialize_entry` and `evaluate_mle`.

## AND Table

For an interleaved address containing the bits of `x` and `y`, the table entry
is:

$$
T_{\mathrm{AND}}(\operatorname{interleave}(x, y)) = x \mathbin{\&} y
$$

The verifier-facing evaluator computes:

$$
\widetilde{T}_{\mathrm{AND}}(r)
=
\sum_{i=0}^{\mathrm{XLEN}-1}
2^{\mathrm{XLEN}-1-i} r_{2i} r_{2i+1}
$$

## Rust Shape

```rust
fn materialize_entry(index: u128) -> u64 {
    let (x, y) = uninterleave_bits(index);
    x & y
}
```

```rust
fn evaluate_mle(r: &[F]) -> F {
    let mut result = F::zero();
    for i in 0..XLEN {
        result += F::from_u64(1u64 << (XLEN - 1 - i))
            * r[2 * i]
            * r[2 * i + 1];
    }
    result
}
```

## First Lean Question

The first proof should show agreement on the Boolean hypercube:

$$
\widetilde{T}_{\mathrm{AND}}(\operatorname{bits}(j)) =
T_{\mathrm{AND}}(j)
$$

The second proof should show that the evaluator is the multilinear extension of
the public table.

## Design Checklist

- [x] Identify `materialize_entry` as the finite table definition.
- [x] Identify `evaluate_mle` as the verifier-facing evaluator.
- [ ] State Boolean-hypercube agreement in Lean.
- [ ] State full MLE correctness in Lean.
- [ ] Decide how this connects to the sum-check constraints.
