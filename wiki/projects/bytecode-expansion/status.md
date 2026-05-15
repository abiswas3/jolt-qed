# Bytecode Expansion Status


Below is a summary of all the instructions that have passing theorems. 
The corresponding `rust` code for all these jolt instructions can be found at: https://github.com/a16z/jolt/tree/main/tracer/src/instruction.



**Overall:** ![closed](https://img.shields.io/badge/closed-40-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-18-yellow) ![todo](https://img.shields.io/badge/todo-9-lightgrey) — **67 instructions total**


## ALU — I-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLLI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Shift/Slli.lean#L68`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Slli.lean#L68) |
| SRLI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Shift/Srli.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srli.lean#L99) |
| SRAI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Shift/Srai.lean#L91`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/Shift/Srai.lean#L91) |

## ALU — R-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLL | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Shift/Sll.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sll.lean#L99) |
| SRL | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Shift/Srl.lean#L90`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Srl.lean#L90) |
| SRA | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Shift/Sra.lean#L89`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/Shift/Sra.lean#L89) |

## ALU — I-type word

![closed](https://img.shields.io/badge/closed-4-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/W/Addiw.lean#L80`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Addiw.lean#L80) |
| SLLIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/W/Slliw.lean#L90`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Slliw.lean#L90) |
| SRLIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/W/Srliw.lean#L164`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Srliw.lean#L164) |
| SRAIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/W/Sraiw.lean#L140`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Itype/W/Sraiw.lean#L140) |

## ALU — R-type word

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Addw.lean#L98`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Addw.lean#L98) |
| SUBW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Subw.lean#L85`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Subw.lean#L85) |
| MULW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Mulw.lean#L91`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Mulw.lean#L91) |
| SRAW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Sraw.lean#L147`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sraw.lean#L147) |
| SLLW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Sllw.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Sllw.lean#L99) |
| SRLW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/W/Srlw.lean#L147`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Rtype/W/Srlw.lean#L147) |

## ALU — multiplication

![closed](https://img.shields.io/badge/closed-2-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| MULH | ![closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) | [`ALUFamily/Mult/Mulh.lean#L352`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Mult/Mulh.lean#L352) |
| MULHSU | ![closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) | [`ALUFamily/Mult/Mulhsu.lean#L648`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUFamily/Mult/Mulhsu.lean#L648) |

## ALU advice (div / rem)

![closed](https://img.shields.io/badge/closed-8-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| DIV | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Div.lean#L305`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Div.lean#L305) |
| DIVU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divu.lean#L220`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Divu.lean#L220) |
| DIVW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divw.lean#L339`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Divw.lean#L339) |
| DIVUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divuw.lean#L222`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Divuw.lean#L222) |
| REM | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Rem.lean#L305`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Rem.lean#L305) |
| REMU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remu.lean#L193`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Remu.lean#L193) |
| REMW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remw.lean#L339`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Remw.lean#L339) |
| REMUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remuw.lean#L230`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/ALUAdviceFamilyRW/Remuw.lean#L230) |

## Advice loads

![closed](https://img.shields.io/badge/closed-5-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADVICE | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`VirtualInstructions.lean#L456`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/VirtualInstructions.lean#L456) |
| ADVICELB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelb.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelb.lean#L47) |
| ADVICELH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelh.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelh.lean#L47) |
| ADVICELW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelw.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Advicelw.lean#L47) |
| ADVICELD | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Adviceld.lean#L24`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AdviceFamily/Adviceld.lean#L24) |

## Loads

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LB_main.lean#L166`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LB_main.lean#L166) |
| LBU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LBU_main.lean#L180`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LBU_main.lean#L180) |
| LH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LH_main.lean#L315`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LH_main.lean#L315) |
| LHU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LHU_main.lean#L270`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LHU_main.lean#L270) |
| LW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LW_main.lean#L355`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LW_main.lean#L355) |
| LWU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LWU_main.lean#L268`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/LoadFamily/LWU_main.lean#L268) |

## Load-reserved

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-2-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LR.W | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| LR.D | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |

## Stores

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sw_main.lean#L296`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/StoreFamily/Sw_main.lean#L296) |
| SH | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sh_main.lean#L233`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/StoreFamily/Sh_main.lean#L233) |
| SB | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sb_main.lean#L245`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/StoreFamily/Sb_main.lean#L245) |

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
| AMOADD.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoaddwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOADD.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoadddProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOAND.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoandwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOAND.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoanddProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoorwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoordProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOXOR.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoxorwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOXOR.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoxordProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOSWAP.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoswapwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOSWAP.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amoswapdProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMIN.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amominwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMIN.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amomindProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMINU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amominuwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMINU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amominudProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMAX.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amomaxwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMAX.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amomaxdProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMAXU.W | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amomaxuwProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |
| AMOMAXU.D | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`amomaxudProgram_eq_sail_aligned`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/EmbeddedSailJoltState/InstructionEquivalence/AtomicFamily/Statements.lean) |

## System

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-5-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ECALL | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| EBREAK | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| MRET | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRW | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
| CSRRS | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
