# Lookup Table Verification

## Goal

Prove that the verifier-facing lookup-table polynomials represent the intended
lookup tables.

## First Target

Start with the `AND` table.

1. Boolean-hypercube agreement:

   ```text
   evaluate_mle_AND(bits(index)) = materialize_entry_AND(index)
   ```

2. Full MLE theorem:

   ```text
   evaluate_mle_AND(r)
     = multilinear extension of materialize_entry_AND
   ```

## Current Status

Status: planning.

## Next Steps

- Write the Lean definition of the AND table.
- State the Boolean-hypercube theorem.
- Decide how generated Rust/MLE artifacts will be represented.

