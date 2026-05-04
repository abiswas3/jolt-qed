# Lookup Table Verification Timeline

## June 

### Targets 

+ [ ] Start formalising lookup table MLE equivalence for some of the simpler instructions `AND, XOR` etc. See [plan](planning/LOOKUP_TABLE_VERIFICATION_PLAN.md)

### What we did:


## July

Goal: bring the AND lookup table into Lean with both definitions ported, and prove the easy half (Boolean-hypercube agreement).

+ [ ] ![Target](https://img.shields.io/badge/target-2026--07--12-yellow) Port the Rust `materialize_entry` for AND into Lean as `T_AND`, mirroring the `uninterleave_bits` shape. See [Design](design.md).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--07--19-yellow) Port the Rust `evaluate_mle` for AND into Lean as `mle_AND`, keeping the polynomial form explicit.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--07--31-yellow) Prove Boolean-hypercube agreement: `mle_AND (bits j) = T_AND j` for every `j`. See [Risks: theorem_shape](risks.md).

## August

Goal: close the full MLE-correctness theorem for AND and decide whether the pattern is ready to repeat on a second table.

+ [ ] ![Target](https://img.shields.io/badge/target-2026--08--16-yellow) Prove full MLE correctness for AND: `mle_AND` is *the* multilinear extension of `T_AND` (uniqueness + Boolean agreement).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--08--23-yellow) Document the proof pattern in `design.md` so it can be re-applied per table.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--08--31-yellow) Port a second table (`XOR`) using the documented pattern as a sanity check. Stop here if the pattern needs revision — fold lessons into the AND proof.

