# Bytecode Expansion Risks

![Type](https://img.shields.io/badge/type-risk_register-24292f)
![Status](https://img.shields.io/badge/status-in_progress-blue)

## Open Risks

### Special Memory Regions Are Not Modeled

![Risk](https://img.shields.io/badge/risk-memory_regions-red)

- Impact: load/store theorem may overclaim.
- Response: add explicit memory-region assumptions.

### Store Semantics Are Incomplete

![Risk](https://img.shields.io/badge/risk-stores-red)

- Impact: blocks full bytecode expansion theorem.
- Response: treat stores as their own proof slice.

### Atomics Are Missing

![Risk](https://img.shields.io/badge/risk-atomics-yellow)

- Impact: blocks August completion target.
- Response: add dedicated atomics milestone.

### Trace Metadata Is Not Modeled

![Risk](https://img.shields.io/badge/risk-trace_metadata-lightgrey)

- Impact: full trace theorem may need extra hypotheses.
- Response: track separately from instruction-local proofs.

### Virtual-Register Renaming Is Informal

![Risk](https://img.shields.io/badge/risk-vreg_renaming-lightgrey)

- Impact: may confuse equivalence statements.
- Response: clean up after the core theorem structure stabilizes.

## Decisions

### Use Semantic Lowering Theorems

- Reason: this matches the structure of recursively expanded instruction sequences.

### Do Not Expand Every Caller From Scratch

- Reason: that would duplicate proofs and make changes brittle.

### State Theorem Assumptions Explicitly

- Reason: the final result should be precise about the modeled execution subset.

## Risk Checklist

- [ ] Add owner for each red risk.
- [ ] Link each risk to the relevant theorem page.
- [ ] Decide which risks block the August completion claim.
