# Bytecode Expansion

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)

- Owner: [abiswas3](https://github.com/abiswas3)

## Summary

The user provides a guest program written in RISC-V assembly along with program inputs to the Jolt zkVM. In return, Jolt hands the user the output and a proof that it ran an "equivalent" program — written in Jolt assembly — correctly. Concretely, the Jolt tracer takes the guest program, translates it into a new program over Jolt's instruction set, and proves that it executed every instruction of *that* program correctly.

For correctness to hold we must show the new program is equivalent to the original guest program. The translation works one guest instruction at a time: every RISC-V instruction `inst` is replaced by a fixed sequence of Jolt virtual + real instructions, the *bytecode expansion* `expand(inst)`. The Jolt program is the concatenation of those expansions, in order. So whole-program equivalence reduces to a per-instruction claim: each expansion must compute the same architectural state transition as the RISC-V instruction it stands in for.

## Formal statement

Let `Sail.run : Inst → State → State` be the trusted RISC-V semantics produced by the Sail-to-Lean transpiler, and let `Jolt.run : List Inst → State → State` be the Jolt execution model running a sequence of (virtual + real) Jolt instructions. For each guest RISC-V instruction `inst` the tracer fixes an expansion `expand(inst) : List Inst`. The per-instruction proof obligation is:

> For every RISC-V instruction `inst` in the supported subset and every starting state `s`,
>
> &nbsp;&nbsp;&nbsp;&nbsp;`Jolt.run (expand inst) s  =  Sail.run inst s`

We discharge this as a single Lean theorem per instruction, named `jolt_<inst>_eq_sail`. Once it is closed for every `inst` in the supported subset, induction over the program lifts it to whole-program equivalence: for any guest program `p`, running `concatMap expand p` under the Jolt model lands in the same final architectural state as running `p` under the trusted Sail spec. That whole-program agreement is the 1:1 mapping the design relies on.

> [!IMPORTANT]
> If the Rust-to-Lean transcription of the Jolt ISA is faithful, and the Lean kernel is to be trusted, then the modified guest program written in Jolt assembly is equivalent to the original RISC-V guest program.

## ALUFamily proof style

As of 2026-05-15, the `ALUFamily` proofs have been restructured into a more human-readable form. The goal of the cleanup was not just to close theorems, but to make the proof scripts explain the bytecode expansion.

The current style separates the proof into three layers:

1. Instruction-local semantic lemmas: each emitted Jolt instruction gets a small lemma exposing the next checkpoint state, the fact that the instruction retires successfully, and the value written by that instruction.
2. Pure value lemmas: the bitvector arithmetic is proved separately from the monadic execution plumbing.
3. Concrete expansion proofs: the main theorem reads as a straight-line trace through named checkpoint states, followed by a final state equation using the pure value lemma.

For example, the `ADDW` proof is organized around the state after the `ADD`, the state after the word sign-extension, the proof that each instruction succeeds, and the mathematical fact that the sign-extended Jolt result is the Sail `ADDW` result. Longer proofs such as `SRAW` follow the same shape with more named intermediate checkpoints rather than a different proof idiom.

This naming and structure is now intended to be the baseline for future ALU bytecode-expansion proofs: names should describe the instruction boundary or value being established, not the mechanics of the tactic script.

## Pages

- [Status](status.md) — per-instruction snapshot: closed, in progress, todo.
- [Timeline](timeline.md) — March–April recap and the May / June roadmap.
- [Risks](risks.md) — issues, blockers, and decisions (to be moved to issues).

## External resources

- [Jolt CPU design in Lean](https://randomwalks.xyz/blog/bytecode-expansions/state/)
- Modularising ALU proofs:
  - [Theorem statement (`ADDW`)](https://randomwalks.xyz/blog/bytecode-expansions/theorem-statement-addw/)
  - [Proof (`ADDW`)](https://randomwalks.xyz/blog/bytecode-expansions/proof-addw/)
  - [Helper lemmas](https://randomwalks.xyz/blog/bytecode-expansions/helpers/)
- Memory pipeline modelling and proof: see Section 4 of the paper draft below.
- [Soundness and completeness of advice ALU instructions](https://randomwalks.xyz/blog/bytecode-expansions/theorem-statement-addw/)
- Paper draft: TODO.
