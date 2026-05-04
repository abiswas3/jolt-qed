# Lookup Table Verification Theorem Plan

![Type](https://img.shields.io/badge/type-theorem_plan-24292f)
![Status](https://img.shields.io/badge/status-planning-yellow)

## First Target: AND

### `materialize_entry` Matches Bitwise AND

![Status](https://img.shields.io/badge/status-planning-yellow)

- Notes: dummy row.

### `evaluate_mle` Agrees on Boolean Points

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: main first theorem.

### `evaluate_mle` Is the Full MLE

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: main polynomial theorem.

### Sum-check Bridge

![Status](https://img.shields.io/badge/status-todo-lightgrey)

- Notes: later theorem relating table consistency checks to CPU semantics.

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

> [!NOTE]
> Boolean-hypercube agreement and full MLE correctness are related but should
> remain separate theorem statements.
