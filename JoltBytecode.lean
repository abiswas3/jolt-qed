-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.


-- Infrastructure
import JoltBytecode.EmbeddedSailJoltState.Defs                                        -- SailJoltState, liftSail, JoltConfig
import JoltBytecode.EmbeddedSailJoltState.RegisterOps                                  -- register lemmas, stateAfterWrite
import JoltBytecode.EmbeddedSailJoltState.RtypeW                                       -- @[spec], generic W-type framework
import JoltBytecode.EmbeddedSailJoltState.ShiftDefs                                    -- ctz, Riscv.*, Jolt.*, shared lemmas

-- ============================================================================
-- Instruction proofs — Format R (register-register)
-- ============================================================================

import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Addw                        -- DONE: ADDW (ADD + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Subw                        -- DONE: SUBW (SUB + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Sllw                        -- DONE: SLLW
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Srlw                        -- DONE: SRLW
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Sraw                        -- DONE: SRAW
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Sll                     -- DONE: SLL
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Srl                     -- DONE: SRL
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.Shift.Sra                     -- DONE: SRA

-- Multiplication
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Mulw                        -- DONE: MULW (MUL + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Mult.Mulh                         -- DONE: MULH (Rust inline sequence)
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulhsu    -- TODO: execute_MUL, signed×unsigned

-- Divide / Remainder [Advice Family RW]
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Div
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Divu
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Divw
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Divuw
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Rem
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Remu
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Remw
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUAdviceFamilyRW.Remuw

-- ============================================================================
-- Instruction proofs — Format I (register-immediate)
-- ============================================================================

import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Addiw                       -- DONE: ADDIW (ADDI + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Shift.Srai                    -- DONE: SRAI
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Sraiw                       -- DONE: SRAIW
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Shift.Slli                    -- DONE: SLLI
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.Shift.Srli                    -- DONE: SRLI
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Slliw                       -- DONE: SLLIW
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Itype.W.Srliw                       -- DONE: SRLIW

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LW_main     -- DONE: LW   (width=4, signed)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LB_main     -- DONE: LB   (width=1, signed)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LBU_main    -- DONE: LBU  (width=1, unsigned)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LH_main     -- DONE: LH   (width=2, signed)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LHU_main    -- DONE: LHU  (width=2, unsigned)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.LoadFamily.LWU_main    -- DONE: LWU  (width=4, unsigned)

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================
-- Store proofs live under `InstructionEquivalence.StoreFamily`.
-- They are not imported here until the duplicate memory-helper names shared
-- with LoadFamily are reconciled.

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.AtomicFamily.Statements

-- Load Reserved
-- LR/SC theorem statements are not yet stated.

-- ============================================================================
-- Instruction proofs — Advice / System / CSR
-- ============================================================================

-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.AdviceFamily.Advicelb  -- advice load byte   DONE:
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.AdviceFamily.Adviceld  -- advice load dword   DONE:
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.AdviceFamily.Advicelh  -- advice load halfword   DONE:
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.AdviceFamily.Advicelw  -- advice load word   DONE:

-- System : Shuld be easy, I'll close when we get to it.
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Csrrs     -- TODO: CSR read-set
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Csrrw     -- TODO: CSR read-write
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Ecall     -- TODO: environment call
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mret      -- TODO: machine return
