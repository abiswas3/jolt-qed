# Lookup Table Verification Risks

## Open Risks

| Risk | Impact | Response |
|---|---|---|
| The table theorem is stated too abstractly | It may not match the Rust verifier code | Start with concrete AND code: `materialize_entry` and `evaluate_mle`. |
| Boolean-hypercube agreement is confused with full MLE correctness | The proof goal becomes unclear | Track these as two separate theorems. |
| Sum-check bridge is attempted too early | The first milestone becomes too large | Prove the table evaluator first. |
| Remaining tables differ structurally | AND proof may not generalize cleanly | Record the proof pattern after AND. |

## Decisions

| Decision | Reason |
|---|---|
| Start with AND | It is concrete, small, and directly tied to existing Rust code. |
| Prove Boolean agreement first | It validates the evaluator against table entries. |
| Prove full MLE theorem second | It explains why the verifier can evaluate the table without materializing it. |
