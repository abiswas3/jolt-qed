# Bytecode Expansion

![Status](https://img.shields.io/badge/status-in_progress-blue)
![Target](https://img.shields.io/badge/target-2026--08--31-green)


The user provides a guest program written in RISC-V assembly and program inputs to the Jolt Zk-vm. 
In return Jolt hands the user the output and a proof that it ran an "equivalent" program written Jolt assembly correctly. 
Thus, the jolt tracer takes the guest program as input, translates it a new program, and proves that it executed every instruction correctly.
For correctness to hold we must show that the the new program is equivalent to the original guest program. 
More specically, we wish to show that there is a 1:1 mapping between jolt program...


## Pages

- [Timeline](timeline.md): milestones, deadlines, and target dates.
- [Design](design.md): technical explanation of how the project works.
- [Risks](risks.md): assumptions, blockers, and decisions.

## Current Task List

+ [ ] ![Target](https://img.shields.io/badge/target-2026--05--10-yellow) Fix the recursive virtual extension issue. See [Risks](risks.md).

+ [ ] 
