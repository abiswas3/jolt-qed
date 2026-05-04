# Lookup Table Verification Theorem Plan

## First Target: AND

| Theorem | Status | Notes |
|---|---|---|
| `materialize_entry` matches bitwise AND | Planning | Dummy row. |
| `evaluate_mle` agrees on Boolean points | Not started | Main first theorem. |
| `evaluate_mle` is the full MLE | Not started | Main polynomial theorem. |
| Sum-check bridge | Not started | Later theorem relating table consistency checks to CPU semantics. |

## Dummy Theorem Shapes

```lean
theorem and_eval_mle_agrees_on_hypercube
    (j : Fin (2 ^ (2 * XLEN))) :
    evalAndMLE (bits j) = materializeAnd j := by
  sorry
```

```lean
theorem and_eval_mle_is_multilinear_extension
    (r : Fin (2 * XLEN) -> F) :
    evalAndMLE r = multilinearExtension materializeAnd r := by
  sorry
```

## Later Bridge

Eventually, the table theorem should connect to the verifier check. Dummy
notation:

$$
\sum_{b \in \{0,1\}^n}
\operatorname{eq}(r, b)
\left(z_b - \widetilde{T}_{\mathrm{AND}}(a_b)\right)
= 0
$$

The actual theorem should use the real Jolt polynomial names.
