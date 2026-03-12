-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.

-- Jolt State model (128 registers, stateful instruction sequences)
import JoltBytecode.JoltInstructions.JoltState
import JoltBytecode.JoltInstructions.JoltOps
import JoltBytecode.JoltInstructions.RiscvState
import JoltBytecode.JoltInstructions.Addw
import JoltBytecode.JoltInstructions.Lw

-- Common definitions
import JoltBytecode.BytecodeExpansions.Common.Cpu
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

-- ============================================================================
-- Instruction proofs — Format R (register-register)
-- ============================================================================

import JoltBytecode.BytecodeExpansions.Instructions.Addw       -- DONE: ADDW
import JoltBytecode.BytecodeExpansions.Instructions.Subw       -- DONE: SUBW
import JoltBytecode.BytecodeExpansions.Instructions.Mulw       -- DONE: MULW
import JoltBytecode.BytecodeExpansions.Instructions.Mulh       -- DONE: MULH
import JoltBytecode.BytecodeExpansions.Instructions.Mulhsu     -- NEXT: sorry in mulhsu_eq_mulhsuJolt (signed×unsigned high multiply)
import JoltBytecode.BytecodeExpansions.Instructions.Sll        -- NEXT: sorry in sll_eq_mul_pow2 (shift = multiply)
import JoltBytecode.BytecodeExpansions.Instructions.Sllw       -- NEXT: sorry in sll_32_eq_mul_trunc (32-bit shift = multiply truncated)
import JoltBytecode.BytecodeExpansions.Instructions.Srl        -- DONE: SRL
import JoltBytecode.BytecodeExpansions.Instructions.Srlw       -- NEXT: sorry in ctz_srlw_bitmask, srlw_eq_srlwJolt
import JoltBytecode.BytecodeExpansions.Instructions.Sra        -- DONE: SRA
import JoltBytecode.BytecodeExpansions.Instructions.Sraw       -- DONE: SRAW
import JoltBytecode.BytecodeExpansions.Instructions.Div        -- TODO: sorry in 3 lemmas (no_overflow, div_validation_sound, div_identity)
-- import JoltBytecode.BytecodeExpansions.Instructions.Divw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Divu    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Divuw   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Remw    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Rem     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Remu    -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Remuw   -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lrd     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lrw     -- TODO: stub only

-- ============================================================================
-- Instruction proofs — Format I (register-immediate)
-- ============================================================================

import JoltBytecode.BytecodeExpansions.Instructions.Addiw      -- DONE: ADDIW
import JoltBytecode.BytecodeExpansions.Instructions.Slli       -- DONE: SLLI
import JoltBytecode.BytecodeExpansions.Instructions.Slliw      -- DONE: SLLIW
import JoltBytecode.BytecodeExpansions.Instructions.Srli       -- DONE: SRLI
import JoltBytecode.BytecodeExpansions.Instructions.Srliw      -- DONE: SRLIW
import JoltBytecode.BytecodeExpansions.Instructions.Srai       -- DONE: SRAI
import JoltBytecode.BytecodeExpansions.Instructions.Sraiw      -- DONE: SRAIW
import JoltBytecode.BytecodeExpansions.Instructions.Csrrw      -- DONE: CSRRW
import JoltBytecode.BytecodeExpansions.Instructions.Csrrs      -- TODO: needs CSR proof (CSR state now available)
import JoltBytecode.BytecodeExpansions.Instructions.Ecall       -- DONE: ECALL
import JoltBytecode.BytecodeExpansions.Instructions.Mret       -- DONE: MRET

-- ============================================================================
-- Instruction proofs — Memory (load)
-- ============================================================================

import JoltBytecode.BytecodeExpansions.Instructions.Lw         -- DONE: LW
-- import JoltBytecode.BytecodeExpansions.Instructions.Lwu     -- NEXT: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lhu     -- TODO: stub only
import JoltBytecode.BytecodeExpansions.Instructions.Lb         -- DONE: LB
-- import JoltBytecode.BytecodeExpansions.Instructions.Lbu     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Lh      -- NEXT: stub only

-- ============================================================================
-- Instruction proofs — Memory (store)
-- ============================================================================

-- import JoltBytecode.BytecodeExpansions.Instructions.Sb      -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Sh      -- TODO: stub only
import JoltBytecode.BytecodeExpansions.Instructions.Sw         -- NEXT:: sorry in 2 splice lemmas
-- import JoltBytecode.BytecodeExpansions.Instructions.Scd     -- TODO: stub only
-- import JoltBytecode.BytecodeExpansions.Instructions.Scw     -- TODO: stub only

-- ============================================================================
-- Instruction proofs — Atomic (AMO)
-- ============================================================================

import JoltBytecode.BytecodeExpansions.Instructions.Amoaddd    -- DONE: AMOADD.D
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

import JoltBytecode.BytecodeExpansions.Instructions.Advicelb   -- DONE: ADVICELB (sorry: sign-ext lemma)
import JoltBytecode.BytecodeExpansions.Instructions.Adviceld   -- DONE: ADVICELD (rfl)
import JoltBytecode.BytecodeExpansions.Instructions.Advicelh   -- DONE: ADVICELH (sorry: sign-ext lemma)
import JoltBytecode.BytecodeExpansions.Instructions.Advicelw   -- DONE: ADVICELW (sorry: sign-ext lemma)
