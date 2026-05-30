# Bytecode Expansion Status


Below is a summary of all tracked bytecode-expansion instructions: passing
theorems, current work, remaining todo items, and instructions marked
`unprovable` against the current generated Sail model.
The corresponding `rust` code for all these jolt instructions can be found at: https://github.com/a16z/jolt/tree/main/tracer/src/instruction.



**Overall:** ![closed](https://img.shields.io/badge/closed-61-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-1-yellow) ![todo](https://img.shields.io/badge/todo-1-lightgrey) — **63 provable instructions total**; ![unprovable](https://img.shields.io/badge/unprovable-4-red) tracked separately


## ALU — I-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLLI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Slli.lean#L68`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Slli.lean#L68) |
| SRLI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Srli.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Srli.lean#L99) |
| SRAI | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Srai.lean#L91`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Srai.lean#L91) |

## ALU — R-type shifts

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SLL | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Sll.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Sll.lean#L99) |
| SRL | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Srl.lean#L90`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Srl.lean#L90) |
| SRA | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Sra.lean#L89`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Sra.lean#L89) |

## ALU — I-type word

![closed](https://img.shields.io/badge/closed-4-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Addiw.lean#L80`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Addiw.lean#L80) |
| SLLIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Slliw.lean#L90`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Slliw.lean#L90) |
| SRLIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Srliw.lean#L164`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Srliw.lean#L164) |
| SRAIW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Itype/Sraiw.lean#L140`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Itype/Sraiw.lean#L140) |

## ALU — R-type word

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADDW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Addw.lean#L98`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Addw.lean#L98) |
| SUBW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Subw.lean#L85`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Subw.lean#L85) |
| MULW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Mulw.lean#L91`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Mulw.lean#L91) |
| SRAW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Sraw.lean#L147`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Sraw.lean#L147) |
| SLLW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Sllw.lean#L99`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Sllw.lean#L99) |
| SRLW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`ALUFamily/Rtype/Srlw.lean#L147`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Rtype/Srlw.lean#L147) |

## ALU — multiplication

![closed](https://img.shields.io/badge/closed-2-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| MULH | ![closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) | [`ALUFamily/Mult/Mulh.lean#L352`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Mult/Mulh.lean#L352) |
| MULHSU | ![closed](https://img.shields.io/badge/closed-2026--05--05-brightgreen) | [`ALUFamily/Mult/Mulhsu.lean#L648`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUFamily/Mult/Mulhsu.lean#L648) |

## ALU advice (div / rem)

![closed](https://img.shields.io/badge/closed-8-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| DIV | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Div.lean#L305`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Div.lean#L305) |
| DIVU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divu.lean#L220`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Divu.lean#L220) |
| DIVW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divw.lean#L339`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Divw.lean#L339) |
| DIVUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Divuw.lean#L222`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Divuw.lean#L222) |
| REM | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Rem.lean#L305`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Rem.lean#L305) |
| REMU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remu.lean#L193`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Remu.lean#L193) |
| REMW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remw.lean#L339`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Remw.lean#L339) |
| REMUW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`ALUAdviceFamilyRW/Remuw.lean#L230`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/ALUAdviceFamilyRW/Remuw.lean#L230) |

## Advice loads

![closed](https://img.shields.io/badge/closed-5-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ADVICE | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`JoltISA/Semantics/Instructions/VirtualAdvice.lean#L18`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/JoltISA/Semantics/Instructions/VirtualAdvice.lean#L18) |
| ADVICELB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelb.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AdviceFamily/Advicelb.lean#L47) |
| ADVICELH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelh.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AdviceFamily/Advicelh.lean#L47) |
| ADVICELW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Advicelw.lean#L47`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AdviceFamily/Advicelw.lean#L47) |
| ADVICELD | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`AdviceFamily/Adviceld.lean#L24`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AdviceFamily/Adviceld.lean#L24) |

## Loads

![closed](https://img.shields.io/badge/closed-6-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LB | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LB_main.lean#L168`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LB_main.lean#L168) |
| LBU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LBU_main.lean#L181`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LBU_main.lean#L181) |
| LH | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LH_main.lean#L293`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LH_main.lean#L293) |
| LHU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LHU_main.lean#L272`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LHU_main.lean#L272) |
| LW | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LW_main.lean#L566`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LW_main.lean#L566) |
| LWU | ![closed](https://img.shields.io/badge/closed-brightgreen) | [`LoadFamily/LWU_main.lean#L282`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadFamily/LWU_main.lean#L282) |

## Load-reserved

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![unprovable](https://img.shields.io/badge/unprovable-2-red) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| LR.W | ![unprovable](https://img.shields.io/badge/unprovable-red) | _blocked by opaque Sail reservation hook_; see [`LoadReservedFamily/Lrw.lean`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadReservedFamily/Lrw.lean) |
| LR.D | ![unprovable](https://img.shields.io/badge/unprovable-red) | _blocked by opaque Sail reservation hook_; see [`LoadReservedFamily/Lrd.lean`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/LoadReservedFamily/Lrd.lean) |

## Stores

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SW | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sw_main.lean#L296`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/StoreFamily/Sw_main.lean#L296) |
| SH | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sh_main.lean#L233`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/StoreFamily/Sh_main.lean#L233) |
| SB | ![closed](https://img.shields.io/badge/closed-2026--05--06-brightgreen) | [`StoreFamily/Sb_main.lean#L245`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/StoreFamily/Sb_main.lean#L245) |

## Store-conditional

![closed](https://img.shields.io/badge/closed-0-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![unprovable](https://img.shields.io/badge/unprovable-2-red) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| SC.W | ![unprovable](https://img.shields.io/badge/unprovable-red) | _blocked by opaque Sail reservation hooks_; see [`StoreConditionalFamily/Scw.lean`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/StoreConditionalFamily/Scw.lean) |
| SC.D | ![unprovable](https://img.shields.io/badge/unprovable-red) | _blocked by opaque Sail reservation hooks_; see [`StoreConditionalFamily/Scd.lean`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/StoreConditionalFamily/Scd.lean) |

## Atomics

![closed](https://img.shields.io/badge/closed-18-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-0-yellow) ![todo](https://img.shields.io/badge/todo-0-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| AMOADD.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoaddw.lean#L168`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoaddw.lean#L168) |
| AMOADD.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoaddd.lean#L123`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoaddd.lean#L123) |
| AMOAND.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoandw.lean#L168`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoandw.lean#L168) |
| AMOAND.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoandd.lean#L123`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoandd.lean#L123) |
| AMOOR.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoorw.lean#L168`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoorw.lean#L168) |
| AMOOR.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoord.lean#L123`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoord.lean#L123) |
| AMOXOR.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoxorw.lean#L168`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoxorw.lean#L168) |
| AMOXOR.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoxord.lean#L123`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoxord.lean#L123) |
| AMOSWAP.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoswapw.lean#L257`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoswapw.lean#L257) |
| AMOSWAP.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amoswapd.lean#L312`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amoswapd.lean#L312) |
| AMOMIN.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amominw.lean#L162`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amominw.lean#L162) |
| AMOMIN.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amomind.lean#L136`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amomind.lean#L136) |
| AMOMINU.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amominuw.lean#L162`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amominuw.lean#L162) |
| AMOMINU.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amominud.lean#L147`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amominud.lean#L147) |
| AMOMAX.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amomaxw.lean#L162`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amomaxw.lean#L162) |
| AMOMAX.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amomaxd.lean#L136`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amomaxd.lean#L136) |
| AMOMAXU.W | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amomaxuw.lean#L162`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amomaxuw.lean#L162) |
| AMOMAXU.D | ![closed](https://img.shields.io/badge/closed-2026--05--26-brightgreen) | [`AtomicFamily/Amomaxud.lean#L136`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/AtomicFamily/Amomaxud.lean#L136) |

## System

![closed](https://img.shields.io/badge/closed-3-brightgreen) ![in progress](https://img.shields.io/badge/in_progress-1-yellow) ![todo](https://img.shields.io/badge/todo-1-lightgrey)

| Instruction | Status | Main theorem |
| --- | --- | --- |
| ECALL | ![closed](https://img.shields.io/badge/closed-2026--05--29-brightgreen) | [`System/Ecall.lean#L180`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/System/Ecall.lean#L180) |
| EBREAK | ![closed](https://img.shields.io/badge/closed-2026--05--30-brightgreen) | [`System/Ebreak.lean#L184`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/System/Ebreak.lean#L184), proved via explicit self-loop/breakpoint relation |
| MRET | ![closed](https://img.shields.io/badge/closed-2026--05--30-brightgreen) | [`System/Mret.lean#L582`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/System/Mret.lean#L582) |
| CSRRW | ![in progress](https://img.shields.io/badge/in_progress-yellow) | [`System/Csrrw.lean#L490`](https://github.com/abiswas3/jolt-qed/blob/jolt-isa/JoltBytecode/InstructionEquivalence/System/Csrrw.lean#L490), stated with explicit CSR/legalizer obligations |
| CSRRS | ![todo](https://img.shields.io/badge/todo-lightgrey) | _not yet stated_ |
