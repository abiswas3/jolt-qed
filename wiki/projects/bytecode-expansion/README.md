# Bytecode Expansion

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)
    
Owner: [abiswas3](https://github.com/abiswas3)


## Summary 

The user provides a guest program written in RISC-V assembly along with program inputs to the Jolt zkVM. In return, Jolt hands the user the output and a proof that it ran an "equivalent" program — written in Jolt assembly — correctly. Concretely, the Jolt tracer takes the guest program, translates it into a new program over Jolt's instruction set, and proves that it executed every instruction of *that* program correctly.

For correctness to hold we must show the new program is equivalent to the original guest program. More specifically, the translation works one guest instruction at a time: every RISC-V instruction `inst` is replaced by a fixed sequence of Jolt virtual + real instructions, the *bytecode expansion* `expand(inst)`. The Jolt program is the concatenation of those expansions, in order. So whole-program equivalence reduces to a per-instruction claim: each expansion must compute the same architectural state transition as the RISC-V instruction it stands in for.

More formally:

Let `Sail.run : Inst → State → State` be the trusted RISC-V semantics produced by the Sail-to-Lean transpiler, and let `Jolt.run : List Inst → State → State` be the Jolt execution model running a sequence of (virtual + real) Jolt instructions. For each guest RISC-V instruction `inst` the tracer fixes an expansion `expand(inst) : List Inst`. The per-instruction proof obligation is:

> For every RISC-V instruction `inst` in the supported subset and every starting state `s`,
>
> &nbsp;&nbsp;&nbsp;&nbsp;`Jolt.run (expand inst) s  =  Sail.run inst s`

We discharge this as a single Lean theorem per instruction, named `jolt_<inst>_eq_sail`. Once it is closed for every `inst` in the supported subset, induction over the program lifts it to whole-program equivalence: for any guest program `p`, running `concatMap expand p` under the Jolt model lands in the same final architectural state as running `p` under the trusted Sail spec. That whole-program agreement is the 1:1 mapping the design relies on.



On completetion, we get the following gurantee: 

>[!Important] If the rust to lean transcription of the Jolt ISA is faithful, and the Lean Kernel is to be trusted, then the modified guest program written in Jolt assembly is equivalent to the original RISC-V guest program. 

## Project Resources

Below are resources that inform how we designed the code till now. 


- [status](status.md): per-instruction snapshot — what's closed, in progress, and todo.
- [timeline](timeline.md): March–April recap and the May / June roadmap.
- [risks](risks.md): issues, risks, and other things to flag in our existing code base (to be moved to issues).


+ Jolt CPU design in Lean: https://randomwalks.xyz/blog/bytecode-expansions/state/ 

+ Modularising ALU proofs: https://randomwalks.xyz/blog/bytecode-expansions/theorem-statement-addw/, https://randomwalks.xyz/blog/bytecode-expansions/proof-addw/ and https://randomwalks.xyz/blog/bytecode-expansions/helpers/.

+ Modelling and proving memory pipeline: See Section 4 of draft below.

+ Proving soundness and completeness of Advice ALU instructions: https://randomwalks.xyz/blog/bytecode-expansions/theorem-statement-addw/

+ Current Draft of paper: TODO: 