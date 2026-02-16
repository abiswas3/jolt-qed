import JoltBytecode.BytecodeExpansions.Instructions.lw
import JoltBytecode.BytecodeExpansions.Common.Virtual

/-!
# SW: RISC-V ≡ Jolt Decomposition

## Instruction (RV32I/RV64I)

`SW rs2, offset(rs1)` stores the lower 32 bits of rs2 to memory at the
word-aligned address `(rs1 + offset) & ~3`.

## Jolt Decomposition

Jolt performs a read-modify-write on the containing dword: load the dword,
splice the new word into the correct 32-bit lane using XOR-AND-XOR masking,
then store the dword back.

```
VirtualAssertWordAlignment  rs1, imm
ADDI           v_address,      rs1,    imm
ANDI           v_dword_addr,   v_address, -8
LD             v_dword,        v_dword_addr, 0
SLLI           v_shift,        v_address, 3
ORI            v_mask,         0, -1
SRLI           v_mask,         v_mask, 32
SLL            v_mask,         v_mask, v_shift
SLL            v_word,         rs2,    v_shift
XOR            v_word,         v_dword, v_word
AND            v_word,         v_word, v_mask
XOR            v_dword,        v_dword, v_word
SD             v_dword_addr,   v_dword, 0
```

## Proof Strategy

Show that byte-level word write equals the dword-level XOR-AND-XOR
read-modify-write, by reducing both sides to Nat arithmetic on
little-endian byte sums.
-/

-- Write a 64-bit dword to memory (little-endian, 8 bytes).
def write_dword (addr : BitVec 64) (val : BitVec 64) (s : State) : State :=
  write_mem_bytes 8 addr val s

-- Jolt's SW decomposition: sequence of RISC-V and virtual instructions.
-- Mirrors the Jolt Rust expansion listed above.
def jolt_sw (rs1 rs2 : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base              := read rs1 s.reg
  let v_address         := Riscv.addi base imm                          -- ADDI v_address, rs1, imm
  let (v_address, s)    := Jolt.virtualAssertWordAlignment v_address s  -- VirtualAssertWordAlignment
  if s.error then s                                                     -- panic: early exit
  else
    let v_dword_addr    := Riscv.andi v_address (-8#64)                -- ANDI v_dword_addr, v_address, -8
    let v_dword         := read_dword v_dword_addr s                   -- LD v_dword, v_dword_addr, 0
    let v_shift         := Riscv.slli v_address 3                      -- SLLI v_shift, v_address, 3
    let v_mask          := Riscv.ori (0#64) (-1#64)                    -- ORI v_mask, 0, -1
    let v_mask          := Riscv.srli v_mask 32                        -- SRLI v_mask, v_mask, 32
    let v_mask          := Riscv.sll v_mask v_shift                    -- SLL v_mask, v_mask, v_shift
    let v_word          := Riscv.sll (read rs2 s.reg) v_shift          -- SLL v_word, rs2, v_shift
    let v_word          := Riscv.xor v_dword v_word                    -- XOR v_word, v_dword, v_word
    let v_word          := Riscv.and v_word v_mask                     -- AND v_word, v_word, v_mask
    let v_dword         := Riscv.xor v_dword v_word                    -- XOR v_dword, v_dword, v_word
    write_dword v_dword_addr v_dword s                                  -- SD v_dword_addr, v_dword, 0

theorem sw_eq (rs1 rs2 : BitVec 5) (imm : BitVec 12) (s : State) :
    Riscv.sw rs1 rs2 imm s = jolt_sw rs1 rs2 imm s := by
  sorry
