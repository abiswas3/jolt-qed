import JoltBytecode.JoltInstructions.JoltState
import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual

/-!
# Jolt Instruction Set

All Jolt instructions as `JoltState → JoltState` transitions.
This combines standard RISC-V instructions and Jolt virtual instructions,
all operating on the 128-register JoltState.

Each instruction reads source operands from the register file,
computes a result, and writes it back — faithfully modeling how the
Jolt tracer executes inline sequences.

## Naming Convention

- `jolt_<INSTR>` : standard RISC-V instruction on JoltState
- `jolt_virtual_<INSTR>` : Jolt virtual instruction on JoltState

All operands are `BitVec 7` register indices (supporting virtual registers).
-/

namespace JoltOps

-- ============================================================================
-- RISC-V Base Integer Instructions on JoltState
-- ============================================================================

/-- ADD rd, rs1, rs2 — rd = rs1 + rs2 -/
def jolt_add (rd rs1 rs2 : BitVec 7) (js : JoltState) : JoltState :=
  let val := read rs1 js.reg + read rs2 js.reg
  { js with reg := write rd val js.reg }

/-- ADDI rd, rs1, imm — rd = rs1 + signext(imm) -/
def jolt_addi (rd rs1 : BitVec 7) (imm : BitVec 12) (js : JoltState) : JoltState :=
  let val := Riscv.addi (read rs1 js.reg) imm
  { js with reg := write rd val js.reg }

/-- ANDI rd, rs1, imm64 — rd = rs1 & imm -/
def jolt_andi (rd rs1 : BitVec 7) (imm : BitVec 64) (js : JoltState) : JoltState :=
  let val := Riscv.andi (read rs1 js.reg) imm
  { js with reg := write rd val js.reg }

/-- SLLI rd, rs1, shamt — rd = rs1 << shamt -/
def jolt_slli (rd rs1 : BitVec 7) (shamt : Nat) (js : JoltState) : JoltState :=
  let val := Riscv.slli (read rs1 js.reg) shamt
  { js with reg := write rd val js.reg }

/-- SRL rd, rs1, rs2 — rd = rs1 >>> rs2[5:0] -/
def jolt_srl (rd rs1 rs2 : BitVec 7) (js : JoltState) : JoltState :=
  let val := Riscv.srl (read rs1 js.reg) (read rs2 js.reg)
  { js with reg := write rd val js.reg }

/-- LD rd, rs1, offset — rd = mem[rs1 + offset] (64-bit load)
    Loads a dword from the address in rs1 (offset = 0 for Jolt's usage). -/
def jolt_ld (rd rs1 : BitVec 7) (js : JoltState) : JoltState :=
  let addr := read rs1 js.reg
  let val := jolt_read_dword addr js
  { js with reg := write rd val js.reg }

-- ============================================================================
-- Jolt Virtual Instructions on JoltState
-- ============================================================================

/-- VirtualAssertWordAlignment — check 4-byte alignment, set error if not -/
def jolt_virtual_assert_word_align (rs1 : BitVec 7) (imm : BitVec 12) (js : JoltState) : JoltState :=
  let addr := Riscv.addi (read rs1 js.reg) imm
  if addr &&& 3#64 ≠ 0#64 then { js with error := true }
  else js

/-- VirtualSignExtendWord rd, rs1 — rd = signext32(rs1) -/
def jolt_virtual_sign_extend_word (rd rs1 : BitVec 7) (js : JoltState) : JoltState :=
  let val := Jolt.virtualSignExtendWord (read rs1 js.reg)
  { js with reg := write rd val js.reg }

end JoltOps
