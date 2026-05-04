# Bytecode Expansion Status

## March – April

We started tracking in May. Below is a summary of the work that got done in March and April. See [notes](design.md) for links to code and documentation.

In March, we transpiled the Sail specification of the RISC-V CPU into Lean using the trusted Sail-to-Lean transpiler from Galois and Cambridge. That gives us a Lean function for every RISC-V instruction whose meaning is exactly what the Sail spec says — our reference semantics. Pipeline details are at [Compiling RISCV-SAIL Into Lean4](https://randomwalks.xyz/blog/sail-to-lean/).

In April, we hand-wrote the Jolt-side execution model on top of that. The Jolt model carries Sail's architectural state alongside a virtual-register file, and defines each *virtual instruction* — the building blocks of Jolt's bytecode expansions — in terms of the same Sail bitvector primitives the trusted CPU model already uses. A Jolt expansion is therefore a Lean program reading and writing the same state the Sail spec does, just through Jolt's virtual ISA.

### What "proving" means here

For every RISC-V instruction Jolt expands, there are two Lean functions: the Jolt-side expansion (a sequence of virtual instructions) and the Sail-side reference (the trusted semantics). The proof obligation is that running them from the same starting state lands in the same ending state — same registers, same memory, same flags. We discharge it as one theorem per instruction (`jolt_<inst>_eq_sail`). Once that theorem is closed, the expansion is sound by construction: anything the Jolt prover accepts must agree with what the Sail spec would have produced.

## May 

+ [ ] Fix the recursive virtual extension issue. See [Risks](risks.md) ![Target](https://img.shields.io/badge/target-2026--05--10-yellow) 

+ [ ] Close remaining ALU and Store instructions. These changed due to recent modularisation efforts.![Target](https://img.shields.io/badge/target-2026--05--14-yellow) 


+ [ ] Update Memory envelope in Lean to accomodate for panic, advice, inputs etc. The currently memory outline treats all regions as RAM. See [Risks](risks.md) ![Target](https://img.shields.io/badge/target-2026--05--17-yellow) 

