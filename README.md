# Formally Verifying Jolt Bytecode Expansions


TODO: Add a bit of an executive summary.

1. [Introduction to Jolt Bytecode Expansions]()
2. [Jolt ISA in Lean]()
3. [Assumptions]() made to close theorems.


## Rust To Lean Extraction

TODO: Details on automatic extraction.

## Lean toolchain compatibility

The repository is pinned to Lean `v4.29.0-rc4`, Mathlib commit
`9d092b118b6f9f777ba67c7a2d2c2bcdd1b52395`, and lean-sail `v3`.

Lean `v4.33.0` was tested with matching Mathlib `v4.33.0` on 17 August 2026.
lean-sail `v3` does not elaborate under Lean 4.33. Updating to lean-sail `v5`
makes Sail itself build, but that release replaces the `PreSail` API consumed by
the generated `LeanRV64D` sources. Upgrading therefore requires regenerating or
porting that trusted layer; changing only `lean-toolchain` is not supported.

## Miscellaneous

1. We could not prove equivalence for certain instructions due to inadequate support on the Sail side. Details can be found [here]().
2. Currently TODO: add instructions do not have automatically extracted program expansions.

## References

1. [Jolt Source Code](): The Lean program expansions are automatically extracted from 


