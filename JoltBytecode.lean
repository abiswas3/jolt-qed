-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.


-- Infrastructure
import JoltBytecode.JoltISA.Environment                                        -- SailJoltState, liftSail, JoltConfig
import JoltBytecode.JoltISA.Semantics.RegisterOps                                  -- register lemmas, stateAfterWrite
import JoltBytecode.InstructionEquivalence.ProofSupport                                       -- @[spec], generic W-type framework
import JoltBytecode.JoltISA.Values.Shift                                    -- ctz, Riscv.*, Jolt.*, shared lemmas

-- ============================================================================
-- Instruction proofs — Format R (register-register)
-- ============================================================================

import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Addw                        -- DONE: ADDW (ADD + VSEW)
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Subw                        -- DONE: SUBW (SUB + VSEW)
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Sllw                        -- DONE: SLLW
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Srlw                        -- DONE: SRLW
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Sraw                        -- DONE: SRAW
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Sll                     -- DONE: SLL
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Srl                     -- DONE: SRL
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Sra                     -- DONE: SRA

-- Multiplication
import JoltBytecode.InstructionEquivalence.ALUFamily.Rtype.Mulw                        -- DONE: MULW (MUL + VSEW)
import JoltBytecode.InstructionEquivalence.ALUFamily.Mult.Mulh                         -- DONE: MULH (Rust inline sequence)
-- import JoltBytecode.InstructionEquivalence.Mulhsu    -- TODO: execute_MUL, signed×unsigned

-- Divide / Remainder [Advice Family RW]
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Div
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divu
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Divuw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Rem
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remu
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remw
import JoltBytecode.InstructionEquivalence.ALUAdviceFamilyRW.Remuw

-- ============================================================================
-- Instruction proofs — Format I (register-immediate)
-- ============================================================================

import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Addiw                       -- DONE: ADDIW (ADDI + VSEW)
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Srai                    -- DONE: SRAI
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Sraiw                       -- DONE: SRAIW
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Slli                    -- DONE: SLLI
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Srli                    -- DONE: SRLI
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Slliw                       -- DONE: SLLIW
import JoltBytecode.InstructionEquivalence.ALUFamily.Itype.Srliw                       -- DONE: SRLIW

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.LoadFamily.LW_main     -- DONE: LW   (width=4, signed)
import JoltBytecode.InstructionEquivalence.LoadFamily.LB_main     -- DONE: LB   (width=1, signed)
import JoltBytecode.InstructionEquivalence.LoadFamily.LBU_main    -- DONE: LBU  (width=1, unsigned)
import JoltBytecode.InstructionEquivalence.LoadFamily.LH_main     -- DONE: LH   (width=2, signed)
import JoltBytecode.InstructionEquivalence.LoadFamily.LHU_main    -- DONE: LHU  (width=2, unsigned)
import JoltBytecode.InstructionEquivalence.LoadFamily.LWU_main    -- DONE: LWU  (width=4, unsigned)

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.StoreFamily.Sb_main     -- DONE: SB   (width=1)
import JoltBytecode.InstructionEquivalence.StoreFamily.Sh_main     -- DONE: SH   (width=2)
import JoltBytecode.InstructionEquivalence.StoreFamily.Sw_main     -- DONE: SW   (width=4)

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoaddd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoandd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoord
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoxord
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoswapd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomind
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxd
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominud
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxud
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoaddw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoandw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoorw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoxorw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amoswapw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amominuw
import JoltBytecode.InstructionEquivalence.AtomicFamily.Amomaxuw

-- Load Reserved
import JoltBytecode.InstructionEquivalence.LoadReservedFamily.Lrw
import JoltBytecode.InstructionEquivalence.LoadReservedFamily.Lrd

-- Store Conditional
import JoltBytecode.InstructionEquivalence.StoreConditionalFamily.Scw
import JoltBytecode.InstructionEquivalence.StoreConditionalFamily.Scd

-- ============================================================================
-- Instruction proofs — Advice / System / CSR
-- ============================================================================

import JoltBytecode.InstructionEquivalence.AdviceFamily.Advicelb  -- advice load byte   DONE:
import JoltBytecode.InstructionEquivalence.AdviceFamily.Adviceld  -- advice load dword   DONE:
import JoltBytecode.InstructionEquivalence.AdviceFamily.Advicelh  -- advice load halfword   DONE:
import JoltBytecode.InstructionEquivalence.AdviceFamily.Advicelw  -- advice load word   DONE:

-- System : Shuld be easy, I'll close when we get to it.
import JoltBytecode.InstructionEquivalence.System.Ecall
import JoltBytecode.InstructionEquivalence.System.Ebreak
import JoltBytecode.InstructionEquivalence.System.Mret
-- import JoltBytecode.InstructionEquivalence.Csrrs     -- TODO: CSR read-set
-- import JoltBytecode.InstructionEquivalence.Csrrw     -- TODO: CSR read-write
