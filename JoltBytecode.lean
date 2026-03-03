-- This module serves as the root of the `JoltBytecode` library.
-- Import modules here that should be built as part of the library.

-- Common definitions
import JoltBytecode.BytecodeExpansions.Common.Cpu
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Common.FormatR
import JoltBytecode.BytecodeExpansions.Common.FormatI
import JoltBytecode.BytecodeExpansions.Common.SimpLemmas

-- ============================================================================
-- Instruction proofs
-- ============================================================================

--Format R (register-register)
import JoltBytecode.BytecodeExpansions.Instructions.Subw       -- DONE: SUBW
import JoltBytecode.BytecodeExpansions.Instructions.Mulh       -- DONE: MULH
import JoltBytecode.BytecodeExpansions.Instructions.Sraw       -- DONE: SRAW
import JoltBytecode.BytecodeExpansions.Instructions.Sra        -- DONE: SRA
import JoltBytecode.BytecodeExpansions.Instructions.Srl        -- DONE: SRL
import JoltBytecode.BytecodeExpansions.Instructions.Mulw       -- DONE: MULW
import JoltBytecode.BytecodeExpansions.Instructions.Sll        -- TODO: sorry in sll_eq_mul_pow2 (shift = multiply)
import JoltBytecode.BytecodeExpansions.Instructions.Sllw       -- TODO: sorry in sll_32_eq_mul_trunc (32-bit shift = multiply truncated)
import JoltBytecode.BytecodeExpansions.Instructions.Srlw       -- TODO: sorry in ctz_srlw_bitmask, srlw_eq_srlwJolt
import JoltBytecode.BytecodeExpansions.Instructions.Mulhsu     -- TODO: sorry in mulhsu_eq_mulhsuJolt (signed×unsigned high multiply)
import JoltBytecode.BytecodeExpansions.Instructions.Div        -- TODO: sorry in 3 lemmas (no_overflow, div_validation_sound, div_identity) (oracle-based DIV)
import JoltBytecode.BytecodeExpansions.Instructions.Addw       -- DONE: ADDW

-- DONE: Format I (register-immediate)
import JoltBytecode.BytecodeExpansions.Instructions.Srliw      -- DONE: SRLIW
import JoltBytecode.BytecodeExpansions.Instructions.Sraiw      -- DONE: SRAIW
import JoltBytecode.BytecodeExpansions.Instructions.Slliw      -- DONE: SLLIW
import JoltBytecode.BytecodeExpansions.Instructions.Addiw      -- DONE: ADDIW
import JoltBytecode.BytecodeExpansions.Instructions.Srli       -- DONE: SRLI
import JoltBytecode.BytecodeExpansions.Instructions.Srai       -- DONE: SRAI
import JoltBytecode.BytecodeExpansions.Instructions.Slli       -- DONE: : SLLI  
import JoltBytecode.BytecodeExpansions.Instructions.Csrrw      -- TODO: needs CSR state modeling
import JoltBytecode.BytecodeExpansions.Instructions.Csrrs      -- TODO: needs CSR state modeling

-- Memory (load/store)
import JoltBytecode.BytecodeExpansions.Instructions.Lw         -- DONE: LW

-- Memory (load/store) - sorry in splice lemmas
-- import JoltBytecode.BytecodeExpansions.Instructions.Sw      -- TODO: sorry in 2 splice lemmas

-- Atomic
import JoltBytecode.BytecodeExpansions.Instructions.Amoaddd    -- DONE: AMOADD.D
