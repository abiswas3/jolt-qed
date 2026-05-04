# Bytecode Expansion Design


The user provides a guest program written in RISC-V assembly and program inputs to the Jolt Zk-vm. 
In return Jolt hands the user the output and a proof that it ran an "equivalent" program written Jolt assembly correctly. 
Thus, the jolt tracer takes the guest program as input, translates it a new program, and proves that it executed every instruction correctly.
For correctness to hold we must show that the the new program is equivalent to the original guest program. 
More specically, we wish to show that there is a 1:1 mapping between jolt program...

## Conventions



> [!TIP]
> The design rule is compositionality: prove each lowering theorem once, then
> reuse it in caller proofs.



## Helpful Resources

TODO: Put in the links. 

+ Jolt CPU design in Lean
+ Modularising ALU proofs
+ Modelling and proving memory pipeline.
+ Proving soundness and completeness of Advice ALU instructions.

+ Current Draft of paper: TODO: 