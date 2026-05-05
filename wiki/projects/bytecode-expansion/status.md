# Bytecode Expansion Status


Below is a summary of all the instructions that have passing theorems. 
The corresponding `rust` code for all these jolt instructions can be found at: https://github.com/a16z/jolt/tree/main/tracer/src/instruction.



**Overall:** ![closed](https://img.shields.io/badge/closed-37-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-21-yellow) ![todo](https://img.shields.io/badge/todo-9-lightgrey) — **67 instructions total**

## ALU — I-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLLI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Slli.lean#L63`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Slli.lean#L63) |
| SRLI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Srli.lean#L86`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srli.lean#L86) |
| SRAI | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/Shift/Srai.lean#L73`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srai.lean#L73) |

## ALU — R-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLL | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Sll.lean#L73`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sll.lean#L73) |
| SRL | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Srl.lean#L79`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Srl.lean#L79) |
| SRA | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/Shift/Sra.lean#L76`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sra.lean#L76) |

## ALU — I-type word

![closed](https://img.shields.io/badge/closed-4-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Addiw.lean#L65`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Addiw.lean#L65) |
| SLLIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Slliw.lean#L71`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Slliw.lean#L71) |
| SRLIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Srliw.lean#L122`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Srliw.lean#L122) |
| SRAIW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Itype/W/Sraiw.lean#L122`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Sraiw.lean#L122) |

## ALU — R-type word

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Addw.lean#L73`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Addw.lean#L73) |
| SUBW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Subw.lean#L55`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Subw.lean#L55) |
| MULW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Mulw.lean#L81`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Mulw.lean#L81) |
| SRAW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Sraw.lean#L81`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sraw.lean#L81) |
| SLLW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Sllw.lean#L75`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sllw.lean#L75) |
| SRLW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Rtype/W/Srlw.lean#L74`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Srlw.lean#L74) |

## ALU — multiplication

![closed](https://img.shields.io/badge/closed-2-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| MULH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Mult/Mulh.lean#L247`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Mult/Mulh.lean#L247) |
| MULHSU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUFamily/Mult/Mulhsu.lean#L439`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Mult/Mulhsu.lean#L439) |

## ALU advice (div / rem)

![closed](https://img.shields.io/badge/closed-8-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| DIV | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Div.lean#L214`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Div.lean#L214) |
| DIVU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divu.lean#L175`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divu.lean#L175) |
| DIVW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divw.lean#L214`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divw.lean#L214) |
| DIVUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Divuw.lean#L175`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Divuw.lean#L175) |
| REM | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Rem.lean#L165`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Rem.lean#L165) |
| REMU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remu.lean#L135`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remu.lean#L135) |
| REMW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remw.lean#L172`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remw.lean#L172) |
| REMUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamily/Remuw.lean#L125`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamily/Remuw.lean#L125) |

## Advice loads

![closed](https://img.shields.io/badge/closed-5-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADVICE | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`VirtualInstructions.lean#L456`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/VirtualInstructions.lean#L456) |
| ADVICELB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelb.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelb.lean#L47) |
| ADVICELH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelh.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelh.lean#L47) |
| ADVICELW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelw.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelw.lean#L47) |
| ADVICELD | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Adviceld.lean#L24`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Adviceld.lean#L24) |

## Loads

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LB_main.lean#L166`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LB_main.lean#L166) |
| LBU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LBU_main.lean#L180`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LBU_main.lean#L180) |
| LH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LH_main.lean#L315`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LH_main.lean#L315) |
| LHU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LHU_main.lean#L270`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LHU_main.lean#L270) |
| LW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LW_main.lean#L355`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LW_main.lean#L355) |
| LWU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LWU_main.lean#L268`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LWU_main.lean#L268) |

## Load-reserved

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-2-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LR.W | ![todo](https://img.shields.io/badge/todo-lightgrey) | [`Lrw.lean`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Lrw.lean) |
| LR.D | ![todo](https://img.shields.io/badge/todo-lightgrey) | [`Lrd.lean`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Lrd.lean) |

## Stores

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-3-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SW | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`SwMonad.lean#L257`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/SwMonad.lean#L257) |
| SH | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Sh.lean#L83`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Sh.lean#L83) |
| SB | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Sb.lean#L80`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Sb.lean#L80) |

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
| AMOADD.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoaddw.lean#L75`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoaddw.lean#L75) |
| AMOADD.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoaddd.lean#L44`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoaddd.lean#L44) |
| AMOAND.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoandw.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoandw.lean#L20) |
| AMOAND.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoandd.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoandd.lean#L20) |
| AMOOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoorw.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoorw.lean#L20) |
| AMOOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoord.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoord.lean#L20) |
| AMOXOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoxorw.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoxorw.lean#L20) |
| AMOXOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoxord.lean#L20`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoxord.lean#L20) |
| AMOSWAP.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoswapw.lean#L24`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoswapw.lean#L24) |
| AMOSWAP.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amoswapd.lean#L33`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amoswapd.lean#L33) |
| AMOMIN.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominw.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominw.lean#L29) |
| AMOMIN.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomind.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomind.lean#L29) |
| AMOMINU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominuw.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominuw.lean#L29) |
| AMOMINU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amominud.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amominud.lean#L29) |
| AMOMAX.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxw.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxw.lean#L29) |
| AMOMAX.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxd.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxd.lean#L29) |
| AMOMAXU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxuw.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxuw.lean#L29) |
| AMOMAXU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`Atomics/Amomaxud.lean#L29`](https://github.com/abiswas3/jolt-qed/blob/main/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/Atomics/Amomaxud.lean#L29) |

## System

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-5-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ECALL | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| EBREAK | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| MRET | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRW | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRS | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |


