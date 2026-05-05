# Lookup Table Verification Risks

![Type](https://img.shields.io/badge/type-risk_register-24292f)
![Status](https://img.shields.io/badge/status-planning-yellow)

## Open Risks

### The Table Theorem Is Stated Too Abstractly

![Risk](https://img.shields.io/badge/risk-too_abstract-red)

- Impact: it may not match the Rust verifier code.
- Response: start with concrete AND code: `materialize_entry` and `evaluate_mle`.

### Boolean-Hypercube Agreement Is Confused With Full MLE Correctness

![Risk](https://img.shields.io/badge/risk-theorem_shape-yellow)

- Impact: the proof goal becomes unclear.
- Response: track these as two separate theorems.

### Sum-check Bridge Is Attempted Too Early

![Risk](https://img.shields.io/badge/risk-sumcheck_too_early-yellow)

- Impact: the first milestone becomes too large.
- Response: prove the table evaluator first.

### Remaining Tables Differ Structurally

![Risk](https://img.shields.io/badge/risk-generalization-lightgrey)

- Impact: AND proof may not generalize cleanly.
- Response: record the proof pattern after AND.

## Decisions

### Start With AND

- Reason: it is concrete, small, and directly tied to existing Rust code.

### Prove Boolean Agreement First

- Reason: it validates the evaluator against table entries.

### Prove Full MLE Theorem Second

- Reason: it explains why the verifier can evaluate the table without materializing it.

## Risk Checklist

- [ ] Add owners for red/yellow risks.
- [ ] Link the exact Rust table file.
- [ ] Record which theorem resolves each risk.
