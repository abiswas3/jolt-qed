-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.


-- Infrastructure
import JoltBytecode.Assumptions                                           -- primitive proof assumptions
import JoltBytecode.JoltISA.MemoryAccess                                  -- pure memory address expressions
import JoltBytecode.Bundles                                               -- proof-facing assumption bundles
import JoltBytecode.InstructionEquivalence.BundleLemmas                                               -- facts proved from primitive assumptions
import JoltBytecode.InstructionEquivalence.Memory.Windows                 -- generic memory fact derivations
import JoltBytecode.InstructionEquivalence.BundleLemmas
import JoltBytecode.InstructionEquivalence.Semantics.RegisterOps                                  -- register lemmas, stateAfterWrite
import JoltBytecode.InstructionEquivalence.ProofSupport                                       -- @[spec], generic W-type framework
import JoltBytecode.JoltISA.Values                                    -- ctz, Riscv.*, jolt_*_value helpers

-- ============================================================================
-- Instruction proofs — Format R (register-register)
-- ============================================================================

import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Addw                        -- DONE: ADDW (ADD + VSEW)
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Subw                        -- DONE: SUBW (SUB + VSEW)
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sllw                        -- DONE: SLLW
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Srlw                        -- DONE: SRLW
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sraw                        -- DONE: SRAW
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sll                     -- DONE: SLL
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Srl                     -- DONE: SRL
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sra                     -- DONE: SRA

-- Multiplication
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Mulw                        -- DONE: MULW (MUL + VSEW)
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Mult.Mulh                         -- DONE: MULH (Rust inline sequence)
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Mult.Mulhsu                       -- DONE: MULHSU (Rust inline sequence)

-- Divide / Remainder [Advice Family RW]
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Div
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Divu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Divw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Divuw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Rem
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Remu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Remw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamilyRW.Remuw

-- ============================================================================
-- Instruction proofs — Format I (register-immediate)
-- ============================================================================

import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Addiw                       -- DONE: ADDIW (ADDI + VSEW)
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srai                    -- DONE: SRAI
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Sraiw                       -- DONE: SRAIW
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Slli                    -- DONE: SLLI
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srli                    -- DONE: SRLI
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Slliw                       -- DONE: SLLIW
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srliw                       -- DONE: SRLIW

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LW_main     -- DONE: LW   (width=4, signed)
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LB_main     -- DONE: LB   (width=1, signed)
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LBU_main    -- DONE: LBU  (width=1, unsigned)
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LH_main     -- DONE: LH   (width=2, signed)
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LHU_main    -- DONE: LHU  (width=2, unsigned)
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LWU_main    -- DONE: LWU  (width=4, unsigned)

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sb_main     -- DONE: SB   (width=1)
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sh_main     -- DONE: SH   (width=2)
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sw_main     -- DONE: SW   (width=4)

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomind
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoorw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxorw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominuw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxuw

-- Store Conditional
import JoltBytecode.InstructionEquivalence.Instructions.StoreConditionalFamily.Scw
import JoltBytecode.InstructionEquivalence.Instructions.StoreConditionalFamily.Scd

-- ============================================================================
-- Instruction proofs — Advice / System / CSR
-- ============================================================================

import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Advicelb  -- advice load byte   DONE:
import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Adviceld  -- advice load dword   DONE:
import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Advicelh  -- advice load halfword   DONE:
import JoltBytecode.InstructionEquivalence.Instructions.AdviceFamily.Advicelw  -- advice load word   DONE:

-- System : Shuld be easy, I'll close when we get to it.
import JoltBytecode.InstructionEquivalence.Instructions.System.Ecall
import JoltBytecode.InstructionEquivalence.Instructions.System.Ebreak
import JoltBytecode.InstructionEquivalence.Instructions.System.Mret
import JoltBytecode.InstructionEquivalence.Instructions.System.Csrrw
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Add
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Addi
import JoltBytecode.InstructionEquivalence.Instructions.Natives.And
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Andi
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Auipc
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Fence
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Ld
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Lui
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Mul
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Mulhu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Or
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Ori
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sd
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Slt
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Slti
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sltiu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sltu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sub
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Xor
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Xori
-- import JoltBytecode.InstructionEquivalence.Instructions.System.Csrrs     -- TODO: CSR read-set
