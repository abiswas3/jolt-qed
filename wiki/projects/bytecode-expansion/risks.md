# Bytecode Expansion Risks

## Open Risks

| Risk | Impact | Response |
|---|---|---|
| Special memory regions are not modeled | Load/store theorem may overclaim | Add explicit memory-region assumptions. |
| Store semantics are incomplete | Blocks full bytecode expansion theorem | Treat stores as their own proof slice. |
| Atomics are missing | Blocks August completion target | Add dedicated atomics milestone. |
| Trace metadata is not modeled | Full trace theorem may need extra hypotheses | Track separately from instruction-local proofs. |
| Virtual-register renaming is informal | May confuse equivalence statements | Clean up after the core theorem structure stabilizes. |

## Decisions

| Decision | Reason |
|---|---|
| Use semantic lowering theorems | This matches the structure of recursively expanded instruction sequences. |
| Do not expand every caller from scratch | That would duplicate proofs and make changes brittle. |
| State theorem assumptions explicitly | The final result should be precise about the modeled execution subset. |
