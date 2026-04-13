-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.

-- Common definitions
-- import JoltBytecode.BytecodeExpansions.Common.Cpu
-- import JoltBytecode.BytecodeExpansions.Common.Riscv
-- import JoltBytecode.BytecodeExpansions.Common.Virtual
-- import JoltBytecode.BytecodeExpansions.Common.FormatR
-- import JoltBytecode.BytecodeExpansions.Common.FormatI
-- import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

-- -- ============================================================================
-- -- Instruction proofs — Format R (register-register)
-- -- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Addw       -- DONE: ADDW
-- import JoltBytecode.BytecodeExpansions.Instructions.Subw       -- DONE: SUBW
-- import JoltBytecode.BytecodeExpansions.Instructions.Mulw       -- DONE: MULW
-- import JoltBytecode.BytecodeExpansions.Instructions.Mulh       -- DONE: MULH
-- import JoltBytecode.BytecodeExpansions.Instructions.Mulhsu     -- NEXT: sorry in mulhsu_eq_mulhsuJolt (signed×unsigned high multiply)
-- import JoltBytecode.BytecodeExpansions.Instructions.Sll        -- NEXT: sorry in sll_eq_mul_pow2 (shift = multiply)
-- import JoltBytecode.BytecodeExpansions.Instructions.Sllw       -- NEXT: sorry in sll_32_eq_mul_trunc (32-bit shift = multiply truncated)
-- import JoltBytecode.BytecodeExpansions.Instructions.Srl        -- DONE: SRL
-- import JoltBytecode.BytecodeExpansions.Instructions.Srlw       -- NEXT: sorry in ctz_srlw_bitmask, srlw_eq_srlwJolt
-- import JoltBytecode.BytecodeExpansions.Instructions.Sra        -- DONE: SRA
-- import JoltBytecode.BytecodeExpansions.Instructions.Sraw       -- DONE: SRAW
-- import JoltBytecode.BytecodeExpansions.Instructions.Div        -- TODO: sorry in 3 lemmas (no_overflow, div_validation_sound, div_identity)
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Divw    -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Divu    -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Divuw   -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Remw    -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Rem     -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Remu    -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Remuw   -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Lrd     -- TODO: stub only
-- -- import JoltBytecode.BytecodeExpansions.Instructions.Lrw     -- TODO: stub only

-- -- ============================================================================
-- -- Instruction proofs — Format I (register-immediate)
-- -- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Addiw      -- DONE: ADDIW
-- import JoltBytecode.BytecodeExpansions.Instructions.Slli       -- DONE: SLLI
-- import JoltBytecode.BytecodeExpansions.Instructions.Slliw      -- DONE: SLLIW
-- import JoltBytecode.BytecodeExpansions.Instructions.Srli       -- DONE: SRLI
-- import JoltBytecode.BytecodeExpansions.Instructions.Srliw      -- DONE: SRLIW
-- import JoltBytecode.BytecodeExpansions.Instructions.Srai       -- DONE: SRAI
-- import JoltBytecode.BytecodeExpansions.Instructions.Sraiw      -- DONE: SRAIW
-- import JoltBytecode.BytecodeExpansions.Instructions.Csrrw      -- DONE: CSRRW
-- import JoltBytecode.BytecodeExpansions.Instructions.Csrrs      -- TODO: needs CSR proof (CSR state now available)
-- import JoltBytecode.BytecodeExpansions.Instructions.Ecall       -- DONE: ECALL
-- import JoltBytecode.BytecodeExpansions.Instructions.Mret       -- DONE: MRET

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Lw      -- DONE: LW (commented: name clash with EmbeddedSailJoltState.Lw)
-- import JoltBytecode.BytecodeExpansions.Instructions.Lwu     -- NEXT: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lhu     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lb      -- DONE: LB (commented: imports Lw transitively)
-- import JoltBytecode.BytecodeExpansions.Instructions.Lbu     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lh      -- NEXT: stub only

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Sb      -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Sh      -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Sw      -- NEXT: sorry in 2 splice lemmas (commented: imports Lw transitively)
-- import JoltBytecode.BytecodeExpansions.Instructions.Scd     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Scw     -- TODO: stub only

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Amoaddd -- DONE: AMOADD.D (commented: imports Lw transitively)
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoaddw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoandd    -- NEXT: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoandw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amomaxud   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amomaxuw   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amomind    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amominud   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amominuw   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amominw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoxord    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoxorw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amomaxd    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amomaxw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoord     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoorw     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoswapd   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Amoswapw   -- TODO: stub only

-- ============================================================================
-- Instruction proofs — Advice (hints)
-- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Advicelb   -- DONE: ADVICELB (sorry: sign-ext lemma)
-- import JoltBytecode.BytecodeExpansions.Instructions.Adviceld   -- DONE: ADVICELD (rfl)
-- import JoltBytecode.BytecodeExpansions.Instructions.Advicelh   -- DONE: ADVICELH (sorry: sign-ext lemma)
-- import JoltBytecode.BytecodeExpansions.Instructions.Advicelw   -- DONE: ADVICELW (sorry: sign-ext lemma)

-- ============================================================================
-- OLD BEGINS
-- ============================================================================
-- SailJoltState: LEGACY manual monadic proofs (field-duplication architecture)
-- Cannot import alongside EmbeddedSailJoltState — name clashes.
-- Build independently: lake build JoltBytecode.SailJoltState.InstructionEquivalence.Addw

-- import JoltBytecode.SailJoltState.Common                       -- Shared infra (no sorry)
-- import JoltBytecode.SailJoltState.RegisterLemmas               -- wX_rX_roundtrip (no sorry)
-- import JoltBytecode.SailJoltState.InstructionEquivalence.Addw  -- DONE: ADDW
-- import JoltBytecode.SailJoltState.InstructionEquivalence.Subw  -- DONE: SUBW
-- import JoltBytecode.SailJoltState.InstructionEquivalence.Addiw -- DONE: ADDIW
-- import JoltBytecode.SailJoltState.InstructionEquivalence.Srai  -- DONE: SRAI
-- import JoltBytecode.SailJoltState.InstructionEquivalence.Sraiw -- DONE: SRAIW

-- ============================================================================
-- OLD ENDS
-- ============================================================================



import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Addw                  -- DONE: ADDW (ADD + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Subw                  -- DONE: SUBW (SUB + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sllw                  -- DONE: SLLW (VirtualPow2W + MUL + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srlw                  -- DONE: SRLW (SLLI 32 + bitmask + VirtualSRL + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sraw                  -- DONE: SRAW (VSEW + ANDI + bitmask + VirtualSRA + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sll                   -- INPROGRESS: SLL main thm (VirtualPow2 + MUL, 2 sorry'd helpers)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srl                   -- INPROGRESS: SRL main thm (bitmask + VirtualSRL, 1 sorry'd helper)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sra                   -- INPROGRESS: SRA main thm (bitmask + VirtualSRA, 1 sorry'd helper)
-- Multiply / Divide / Remainder
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulw      -- TODO: execute_MULW, truncate + multiply
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulh      -- TODO: execute_MUL, upper-half multiply
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulhsu    -- TODO: execute_MUL, signed×unsigned
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Div       -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divu      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divw      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divuw     -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Rem       -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remu      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remw      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remuw     -- TODO: needs advice

-- Format I W-variants (shift-immediate word)
import JoltBytecode.SailJoltState.Sraiw                        -- DONE: SRAIW (requires rd ≠ x0)
--
-- TODO: SLLI, SRLI — were clean (trivial via liftSail_project), deleted, need recreation
-- TODO: SLLIW, SRLIW — need shift-truncation BitVec lemmas, deleted, need recreation
-- TODO: Port remaining Instructions/ proofs to SailJoltState/
--       (Mulw, Div, Lw, Sw, AMO, CSR, memory instructions)
-- ============================================================================
-- THe CURRENT!!
-- ============================================================================
-- EmbeddedSailJoltState: mvcgen Sail ↔ Jolt proofs (PRIMARY)
--
-- Embedded SailJoltState (sail : SailState + vregs).
-- @[spec] Hoare triples + mvcgen automates monadic plumbing.
-- Theorem shape: projectResult(jolt_X.run js) = sail_X.run js.sail
-- Requires WellFormed (registers initialized).
-- Load instructions also require JoltConfig (M-mode, flat memory).
-- ============================================================================
-- ============================================================================

-- Infrastructure
import JoltBytecode.EmbeddedSailJoltState.Defs                                        -- SailJoltState, liftSail, JoltConfig
import JoltBytecode.EmbeddedSailJoltState.RegisterOps                                  -- register lemmas, stateAfterWrite
import JoltBytecode.EmbeddedSailJoltState.RtypeW                                       -- @[spec], generic W-type framework

-- ============================================================================
-- Instruction proofs — Format R (register-register)
-- ============================================================================

import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Addw                  -- DONE: ADDW (ADD + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Subw                  -- DONE: SUBW (SUB + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sllw                  -- DONE: SLLW (VirtualPow2W + MUL + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srlw                  -- DONE: SRLW (SLLI 32 + bitmask + VirtualSRL + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sraw                  -- DONE: SRAW (VSEW + ANDI + bitmask + VirtualSRA + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sll                   -- DONE: SLL main thm (VirtualPow2 + MUL, 2 sorry'd helpers)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srl                   -- DONE: SRL main thm (bitmask + VirtualSRL, 1 sorry'd helper)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sra                   -- DONE: SRA main thm (bitmask + VirtualSRA, 1 sorry'd helper)
-- Multiply / Divide / Remainder
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulw      -- TODO: execute_MULW, truncate + multiply
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulh      -- TODO: execute_MUL, upper-half multiply
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mulhsu    -- TODO: execute_MUL, signed×unsigned
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Div       -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divu      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divw      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Divuw     -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Rem       -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remu      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remw      -- TODO: needs advice
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Remuw     -- TODO: needs advice

-- ============================================================================
-- Instruction proofs — Format I (register-immediate)
-- ============================================================================

import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Addiw                 -- DONE: ADDIW (ADDI + VSEW)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srai                  -- DONE: SRAI (bitmask shift)
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sraiw                 -- DONE: SRAIW (3-step via virtual regs)
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Slli      -- TODO: like SRAI
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srli      -- TODO: like SRAI
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Slliw     -- TODO: like SRAIW
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Srliw     -- TODO: like SRAIW

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================

import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lw                    -- INPROGRESS: LW main thm passes, 5 sorry'd memory bridge helpers
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lb        -- TODO: width=1, signed
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lbu       -- TODO: width=1, unsigned
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lh        -- TODO: width=2, signed
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lhu       -- TODO: width=2, unsigned
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lwu       -- TODO: width=4, unsigned
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Ld        -- TODO: width=8

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================

-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sb        -- TODO: store byte
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sh        -- TODO: store halfword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Sw        -- TODO: store word

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================

-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoaddd   -- TODO: atomic add dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoaddw   -- TODO: atomic add word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoandd   -- TODO: atomic and dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoandw   -- TODO: atomic and word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amomaxd   -- TODO: atomic max dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amomaxud  -- TODO: atomic max unsigned dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amomaxuw  -- TODO: atomic max unsigned word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amomaxw   -- TODO: atomic max word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amomind   -- TODO: atomic min dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amominud  -- TODO: atomic min unsigned dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amominuw  -- TODO: atomic min unsigned word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amominw   -- TODO: atomic min word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoord    -- TODO: atomic or dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoorw    -- TODO: atomic or word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoswapd  -- TODO: atomic swap dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoswapw  -- TODO: atomic swap word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoxord   -- TODO: atomic xor dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Amoxorw   -- TODO: atomic xor word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lrd       -- TODO: load reserved dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Lrw       -- TODO: load reserved word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Scd       -- TODO: store conditional dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Scw       -- TODO: store conditional word

-- ============================================================================
-- Instruction proofs — Advice / System / CSR
-- ============================================================================

-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Advicelb  -- TODO: advice load byte
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Adviceld  -- TODO: advice load dword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Advicelh  -- TODO: advice load halfword
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Advicelw  -- TODO: advice load word
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Csrrs     -- TODO: CSR read-set
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Csrrw     -- TODO: CSR read-write
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Ecall     -- TODO: environment call
-- import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.Mret      -- TODO: machine return
