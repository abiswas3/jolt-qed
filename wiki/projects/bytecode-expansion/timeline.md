# Bytecode Expansion Status


Below is a summary of all the instructions that have passing theorems. 
The corresponding `rust` code for all these jolt instructions can be found at: https://github.com/a16z/jolt/tree/main/tracer/src/instruction.



**Overall:** ![closed](https://img.shields.io/badge/closed-33-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-23-yellow) ![todo](https://img.shields.io/badge/todo-11-lightgrey) — **67 instructions total**

## ALU — I-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLLI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Slli.lean#L63`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Slli.lean#L63) |
| SRLI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Srli.lean#L86`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srli.lean#L86) |
| SRAI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Srai.lean#L73`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srai.lean#L73) |

## ALU — R-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLL | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Sll.lean#L73`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sll.lean#L73) |
| SRL | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Srl.lean#L79`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Srl.lean#L79) |
| SRA | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Sra.lean#L76`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sra.lean#L76) |

## ALU — I-type word

![closed](https://img.shields.io/badge/closed-4-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Addiw.lean#L65`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Addiw.lean#L65) |
| SLLIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Slliw.lean#L71`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Slliw.lean#L71) |
| SRLIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Srliw.lean#L122`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Srliw.lean#L122) |
| SRAIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Sraiw.lean#L122`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Sraiw.lean#L122) |

## ALU — R-type word

![closed](https://img.shields.io/badge/closed-4-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-2-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Addw.lean#L73`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Addw.lean#L73) |
| SUBW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Subw.lean#L55`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Subw.lean#L55) |
| MULW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Mulw.lean#L81`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Mulw.lean#L81) |
| SRAW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Sraw.lean#L81`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sraw.lean#L81) |
| SLLW | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`ALUFamily/Rtype/W/Sllw.lean#L77`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sllw.lean#L77) |
| SRLW | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`ALUFamily/Rtype/W/Srlw.lean#L75`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Srlw.lean#L75) |

## ALU — multiplication

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-2-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| MULH | ![todo](https://img.shields.io/badge/todo-lightgrey) | [`ALUFamily/Mult/Mulh.lean`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Mult/Mulh.lean) |
| MULHSU | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |

## ALU advice (div / rem)

![closed](https://img.shields.io/badge/closed-8-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| DIV | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Div.lean#L214`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Div.lean#L214) |
| DIVU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divu.lean#L175`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divu.lean#L175) |
| DIVW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divw.lean#L214`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divw.lean#L214) |
| DIVUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divuw.lean#L175`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divuw.lean#L175) |
| REM | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Rem.lean#L165`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Rem.lean#L165) |
| REMU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remu.lean#L135`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remu.lean#L135) |
| REMW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remw.lean#L172`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remw.lean#L172) |
| REMUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remuw.lean#L125`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remuw.lean#L125) |

## Advice loads

![closed](https://img.shields.io/badge/closed-5-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADVICE | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`VirtualInstructions.lean#L456`](../../../JoltBytecode/EmbeddedSailJoltState/VirtualInstructions.lean#L456) |
| ADVICELB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelb.lean#L47`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelb.lean#L47) |
| ADVICELH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelh.lean#L47`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelh.lean#L47) |
| ADVICELW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelw.lean#L47`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelw.lean#L47) |
| ADVICELD | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Adviceld.lean#L24`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Adviceld.lean#L24) |

## Loads

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LB_main.lean#L166`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LB_main.lean#L166) |
| LBU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LBU_main.lean#L180`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LBU_main.lean#L180) |
| LH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LH_main.lean#L315`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LH_main.lean#L315) |
| LHU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LHU_main.lean#L270`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LHU_main.lean#L270) |
| LW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LW_main.lean#L355`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LW_main.lean#L355) |
| LWU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LWU_main.lean#L268`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LWU_main.lean#L268) |

## Load-reserved

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-2-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LR.W | ![todo](https://img.shields.io/badge/todo-lightgrey) | [`Lrw.lean`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Lrw.lean) |
| LR.D | ![todo](https://img.shields.io/badge/todo-lightgrey) | [`Lrd.lean`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Lrd.lean) |

## Stores

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-3-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SW | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`SwMonad.lean#L257`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/SwMonad.lean#L257) |
| SH | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Sh.lean#L83`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Sh.lean#L83) |
| SB | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Sb.lean#L80`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Sb.lean#L80) |

## Store-conditional

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-2-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SC.W | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| SC.D | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |

## Atomics

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-18-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| AMOADD.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoaddw.lean#L75`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoaddw.lean#L75) |
| AMOADD.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoaddd.lean#L44`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoaddd.lean#L44) |
| AMOAND.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoandw.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoandw.lean#L20) |
| AMOAND.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoandd.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoandd.lean#L20) |
| AMOOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoorw.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoorw.lean#L20) |
| AMOOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoord.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoord.lean#L20) |
| AMOXOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoxorw.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoxorw.lean#L20) |
| AMOXOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoxord.lean#L20`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoxord.lean#L20) |
| AMOSWAP.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoswapw.lean#L24`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoswapw.lean#L24) |
| AMOSWAP.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoswapd.lean#L33`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoswapd.lean#L33) |
| AMOMIN.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominw.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominw.lean#L29) |
| AMOMIN.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomind.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomind.lean#L29) |
| AMOMINU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominuw.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominuw.lean#L29) |
| AMOMINU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominud.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominud.lean#L29) |
| AMOMAX.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxw.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxw.lean#L29) |
| AMOMAX.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxd.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxd.lean#L29) |
| AMOMAXU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxuw.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxuw.lean#L29) |
| AMOMAXU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxud.lean#L29`](../../../JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxud.lean#L29) |

## System

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-5-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ECALL | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| EBREAK | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| MRET | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRW | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRS | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |





## March – April

We started tracking in May. Below is a summary of the work that got done in March and April. See [notes](design.md) for links to code and documentation.

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


