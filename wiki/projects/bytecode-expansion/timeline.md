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

+ [x] State and prove `MULH` and `MULHSU` via the unsigned-high-multiply + sign-correction decompositions outlined in `Mulh.lean` and `Mulhsu.lean`.
  ![Closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) Proved `mulhProgram_eq_sail` and `mulhsuProgram_eq_sail` for the `JoltISA.mulhProgram` and `JoltISA.mulhsuProgram` interpreters, with the legacy `jolt_*` theorem names retained as wrappers.

+ [x] Close the two `Bridges/Shift.lean` sorries (`sll_32_eq_mul_trunc`, `ctz_srlw_bitmask`) so `SLLW` and `SRLW` become sorry-free.
  ![Closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) Proved the SLLW/SRLW bridge lemmas in `ALUFamily/Bridges/Shift.lean`, closing the main `SLLW` and `SRLW` equivalence theorems.

+ [x] Close the load family in the new program-block proof style.
  ![Closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) The load proofs now use the three-part reduction pattern: Jolt program blocks, Sail-side reduction, and a pure memory/bitvector bridge. This became the template used for the store-family rewrite.

+ [x] Remove stale load/advice compatibility surfaces from the root build.
  ![Closed](https://img.shields.io/badge/closed-2026--05--15-brightgreen) The load family now exposes only the `JoltISA.*Program` theorem surface in the active files. The old `LoadFamily/*_decomposed.lean` files, `JoltISA/Semantics/Compatibility.lean`, and `VirtualInstructions.lean` were removed; load-alignment run lemmas now live with instruction semantics, and the advice-load proofs are imported through `AdviceFamily/Advice.lean`.

+ [x] Move the main non-advice ALU theorem fronts onto the new `JoltISA` program architecture.
  ![Closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) The I-type shift, R-type shift, I-type word, and R-type word families now have passing theorem statements in the newer style. The older advice-ALU monadic files remain useful history, but they are stale as the main proof architecture.

+ [x] Rewrite the advice ALU family in the new `JoltISA.Program` style.
  ![Closed](https://img.shields.io/badge/closed-2026--05--11-brightgreen) Added `ALUAdviceFamilyRW`, where the advice-backed division and remainder expansions are written as explicit Jolt programs. This matches the newer proof architecture and makes the family more translation-friendly.

+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--17-yellow) Centralise the memory envelope: introduce `JoltFlatMemoryEnvelope` and rewrite load/store theorems to use it. See [Risks: memory_envelope](risks.md).

+ [x] Close the store family (`SB`, `SH`, `SW`) in the new `JoltISA` architecture.
  ![Closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) Added Rust-faithful store expansion programs plus shared store program blocks and splice bridges. The public `SB`, `SH`, and `SW` equivalence theorems now pass in `StoreFamily/{Sb,Sh,Sw}_main.lean`.
  ![Artifact](https://img.shields.io/badge/artifact-2026--05--19-blue) Repaired the Store family after enforcing the Jolt-ISA boundary: Store expansions now use final trace rows plus `slliBlock`, `sllBlock`, and `srliBlock`; the Store proof files no longer mention source rows such as `.SLL`, `.SLLI`, `.SRLI`, or the old store-alignment pseudo-instruction.

+ [x] Remove recursive inline expansion from the Jolt-ISA layer.
  ![Closed](https://img.shields.io/badge/closed-2026--05--19-brightgreen) Restricted `JoltISA.Instr` to final trace-row instructions and represented source instructions that inline through named expansion blocks. The recursive issue is now handled compositionally: expansions call block programs, and block lemmas relate those programs to the old proof phases.

+ [x] Handle Rust's `rd = x0` dispatch for pure writeback instructions.
  ![Partially closed](https://img.shields.io/badge/partial-2026--05--19-orange) Pure non-side-effecting writebacks now use Rust's no-op replacement path, `ADDI x0, x0, 0`, instead of needing an `rd ≠ x0` theorem shape. Side-effecting instructions are still open because Rust handles them by virtual-register remapping rather than by the pure no-op rule. See [Risks: rd_x0](risks.md).

## June

Goal: extend coverage to the atomic, load-reserved, store-conditional, and remaining multiplication families on top of the May infrastructure.

+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--07-yellow) Close `AMOSWAP.W/D`, `AMOAND.W/D`, `AMOOR.W/D`, `AMOXOR.W/D` (the eight degenerate-splice atomics) using the SW splice and centralised memory envelope.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--14-yellow) Close `AMOADD.W/D`, `AMOMIN.W/D`, `AMOMINU.W/D`, `AMOMAX.W/D`, `AMOMAXU.W/D` (the ten arithmetic atomics).
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--18-yellow) State and prove `LR.W` and `LR.D` on top of the closed `LW` / `LD` theorems.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--22-yellow) State and prove `SC.W` and `SC.D` on top of the SW splice + reservation set.
+ [ ] ![Target](https://img.shields.io/badge/target-2026--06--30-yellow) Decide scope for the system instructions (`ECALL`, `EBREAK`, `MRET`, `CSRRW`, `CSRRS`) — either state stub theorems or document them as out-of-scope for the August claim.
