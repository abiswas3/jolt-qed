# Bytecode Expansion Timeline

For the current instruction-by-instruction status snapshot, see [status](status.md).

## March – April

We started tracking in May. Below is a summary of the work that got done in March and April. See the [external resources](README.md#external-resources) section of the project README for blog posts and the paper draft.

In March and April, we transpiled the Sail specification of the RISC-V CPU into Lean using the trusted Sail-to-Lean transpiler from Galois and Cambridge. That gives us a Lean function for every RISC-V instruction whose meaning is exactly what the Sail spec says — our reference semantics. Pipeline details are at [Compiling RISCV-SAIL Into Lean4](https://randomwalks.xyz/blog/sail-to-lean/).
We hand-wrote the Jolt-side execution model on top of that. The Jolt model carries Sail's architectural state alongside a virtual-register file, and defines each *virtual instruction* — the building blocks of Jolt's bytecode expansions — in terms of the same Sail bitvector primitives the trusted CPU model already uses. A Jolt expansion is therefore a Lean program reading and writing the same state the Sail spec does, just through Jolt's virtual ISA.

### What "proving" means here

For every RISC-V instruction Jolt expands, there are two Lean functions: the Jolt-side expansion (a sequence of virtual instructions) and the Sail-side reference (the trusted semantics). The proof obligation is that running them from the same starting state lands in the same ending state — same registers, same memory, same flags. We discharge it as one theorem per instruction (`jolt_<inst>_eq_sail`). Once that theorem is closed, the expansion is sound by construction: anything the Jolt prover accepts must agree with what the Sail spec would have produced.

>![IMPORTANT] We are assuming that our transcription of the rust expansion into is faithfu.


## May

Goal: close every red-risk item that doesn't depend on a structural rewrite, and finish the in-progress ALU + store proofs.

+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--10-yellow) Fix the recursive virtual-extension issue — prove compositional lowering theorems and use them in caller proofs. See [Risks: recursive_expansion](risks.md).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--14-yellow) Close the two `Bridges/Shift.lean` sorries (`sll_32_eq_mul_trunc`, `ctz_srlw_bitmask`) so `SLLW` and `SRLW` become sorry-free.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--17-yellow) Centralise the memory envelope: introduce `JoltFlatMemoryEnvelope` and rewrite load/store theorems to use it. See [Risks: memory_envelope](risks.md).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--24-yellow) Discharge the two `SwMonad.lean` prefix-success lemmas, then instantiate the splice argument for `SH` and `SB` on top of `xor_and_xor_splice`.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--31-yellow) Add `rd = x0` wrapper theorems where Rust handles the case explicitly — covers no-op replacement and side-effecting remaps. See [Risks: rd_x0](risks.md).

## June

Goal: extend coverage to the atomic, load-reserved, store-conditional, and remaining multiplication families on top of the May infrastructure.

+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--07-yellow) Close `AMOSWAP.W/D`, `AMOAND.W/D`, `AMOOR.W/D`, `AMOXOR.W/D` (the eight degenerate-splice atomics) using the SW splice and centralised memory envelope.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--14-yellow) Close `AMOADD.W/D`, `AMOMIN.W/D`, `AMOMINU.W/D`, `AMOMAX.W/D`, `AMOMAXU.W/D` (the ten arithmetic atomics).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--18-yellow) State and prove `LR.W` and `LR.D` on top of the closed `LW` / `LD` theorems.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--22-yellow) State and prove `SC.W` and `SC.D` on top of the SW splice + reservation set.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--27-yellow) State and prove `MULH` and `MULHSU` via the unsigned-high-multiply + sign-correction decomposition outlined in `Mulh.lean`.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--30-yellow) Decide scope for the system instructions (`ECALL`, `EBREAK`, `MRET`, `CSRRW`, `CSRRS`) — either state stub theorems or document them as out-of-scope for the August claim.
