# JoltBytecode

Formal verification of [Jolt](https://github.com/a16z/jolt)'s RISC-V bytecode expansion equivalences in [Lean 4](https://lean-lang.org/) + [Mathlib](https://github.com/leanprover-community/mathlib4).

> [!WARNING]
> This project uses `leanprover/lean4:v4.29.0-rc4` to be compatible with both Mathlib and [lean-sail](https://github.com/rems-project/lean-sail) (v3). The lean-sail dependency targets `nightly-2026-03-05`, but that nightly has no cached Mathlib build. We use `v4.29.0-rc4` as the closest stable toolchain with Mathlib cache available. Lean-sail compiles cleanly under this toolchain despite the minor version mismatch.
>
> **mvcgen limitation:** The `mvcgen` tactic (`Std.Tactic.Do`) and `EStateM.of_wp_run_eq` for weakest-precondition reasoning over `EStateM` do-blocks are available in `v4.29.0-rc6+` but not in `rc4`. Some SailJoltState proofs involving virtual register plumbing (`writeVReg`/`readVReg`) are sorry'd pending this toolchain bump. The mathematical bridge lemmas are fully proved; only the monadic threading is blocked.
