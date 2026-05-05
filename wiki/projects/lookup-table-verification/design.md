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

### Sketch in Lean

```lean
variable (F : Type*) [CommRing F] (XLEN : ℕ)

/-- Concrete table entry, mirroring Rust `materialize_entry`. -/
def T_AND (idx : BitVec (2 * XLEN)) : BitVec XLEN :=
  let (x, y) := uninterleave_bits idx
  x &&& y

/-- Verifier-facing evaluator, mirroring Rust `evaluate_mle`. -/
def mle_AND (r : Fin (2 * XLEN) → F) : F :=
  ∑ i : Fin XLEN,
    (2 ^ (XLEN - 1 - i.val) : F) *
      r ⟨2 * i.val,     by omega⟩ *
      r ⟨2 * i.val + 1, by omega⟩

/-- (1) Boolean-hypercube agreement: on bit-decomposed indices, the evaluator
    returns the concrete table entry. -/
theorem mle_AND_eq_T_AND_on_bits
    (j : BitVec (2 * XLEN)) :
    mle_AND F XLEN (fun k => if j.getLsb k then (1 : F) else 0)
      = ((T_AND XLEN j).toNat : F) := by
  sorry

/-- (2) Full MLE correctness: `mle_AND` *is* the multilinear extension of the
    table over the Boolean hypercube. -/
theorem mle_AND_is_MLE_of_T_AND :
    IsMultilinearExtension
      (mle_AND F XLEN)
      (fun j : BitVec (2 * XLEN) => ((T_AND XLEN j).toNat : F)) := by
  sorry
```

`IsMultilinearExtension` here stands for the predicate "polynomial is multilinear
*and* agrees with the table on every Boolean point" — by uniqueness of the MLE,
(2) follows from (1) plus a multilinearity check on `mle_AND`.

## Design Checklist

- [x] Identify `materialize_entry` as the finite table definition.
- [x] Identify `evaluate_mle` as the verifier-facing evaluator.
- [ ] State Boolean-hypercube agreement in Lean.
- [ ] State full MLE correctness in Lean.
- [ ] Decide how this connects to the sum-check constraints.
