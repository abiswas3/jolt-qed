# Jolt Qed: Formally Verifying The Jolt Zk-VM

This repository contains proofs written using the Lean theorem proving assistant, towards formally verifying the completeness and soundness of the [Jolt zk-VM](https://github.com/a16z/jolt).
The project is _still on-going_, and as Jolt is a relatively complex piece of software, we decompose the task of formally verifying Jolt into the following components.
Blocks in green are complete. Blocks in yellow are in-progress and, greyed out boxes are not yet started.
See [CONTRIBUTING](CONTRIBUTING.md) for information about how to contribute to this project.

```mermaid
flowchart LR
    A["Bytecode Expansion"] --> B["Jolt Constraints"] --> C["Jolt Sumchecks"] --> D["Jolt Reductions"] --> E["Commitment Scheme"]

    classDef complete fill:#22c55e,stroke:#15803d,stroke-width:2px,color:#ffffff
    classDef inprogress fill:#fef3c7,stroke:#d97706,stroke-width:3px,stroke-dasharray:8 4,color:#92400e
    classDef pending fill:#f3f4f6,stroke:#9ca3af,stroke-width:2px,color:#6b7280

    class A complete
    class B inprogress
    class C,D,E pending

```

Explicit details about each component, and current progress can be found [here](https://randomwalks.xyz/blog/jolt-qed/). 
The self contained manuscript describing the efforts of formally verifying is available [here](paper.pdf)

If you wanted to dig around the source code.
[This file](jolt-qed/JoltBytecode/RiscvInstruction.lean) serves as the main entry point for the bytecode expansion project.
It contains 3 large match blocks. 
Loosely, it says given a RISC-V instruction, here is 

1. The list of assumptions we make to prove equivalence for this instruction.
2. Here is the theorem statement we wish to prove.
3. Here is the proof for the above theorem statement. 

There were 67 expandable RISC-V instructions. 
Only 60 of them were proven. Details about why the remaining seven instructions were unprovable is given in Section 7 of the pre-print.

## AI Usage And Miscellany

As is the case for most projects in present times, AI agents assisted us in writing several proofs.
We did not any use a special AI-Lean skill, software, or any MCP servers (perhaps there are better ways to do this).
Our process so far has involved opening two panes in a terminal, one with a Neovim editor of the source code equipped with a Lean LSP, and the other pane with Codex or Claude.
The chats were free form.

TODO: Insert picture here

The most frequently used pattern that we found useful was the following.
A lot of the theorems in the bytecode expansion project are very similar. 
For instance the work done to prove equivalence of `LWU` and `LW` RISC-V instructions is nearly identical. 
They differ in the last step in the application of sign vs unsigned extension. 
Often, we carefully prove `LW` with comments, and make the proof easily readable (see `LB_main.lean` for example). 
Then, we tell the ai agent to complete the proof for `LW` following the exact principles and style. 
It seemed to be able to close the theorems with very limited guidance. 
This strategy has proven to be extremely valuable so far. 

On the other hand, we found that agents were not as good at designing definitions from scratch. 
It took a lot of back and forth, and iterations for the ISA to reach its current state.
So for the Jolt-ISA definition, almost all of it was written by hand, then the AI-agents was asked to do formatting, and check against the rust code. 
It took a few iterations for us to get the final version.
As an effort to enforce human eyes on all critical components of the code, all comments and documentation about the ISA are hand-written.

This project was completed over a span of two and a half months, during which we learned a great deal about Lean. 
Different proofs were written at different phases.
This means that some theorems are more human readable than others (though all pass, so this does not matter if that's all one cares about).
The goal was always to first have a passing proof for the correct theorem statement.
Often we let an AI agent loose to close the theorem by whatever means necessary. 
Then, we explored the output and made proofs simpler, or more human like (akin to how one would proof things on paper, though this is not always possible).
We would eventually like to do this for all proofs, but in the interest of time, we have not yet done this. 
Contributions which make proofs shorter and more human readable are **always** welcome.

