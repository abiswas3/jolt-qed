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
little-endian byte sums. The outer structure mirrors `lw_eq`: case split
on alignment (misaligned = both panic), then case split on dword alignment
(shift = 0 or shift = 32). The key lemma `write_word_eq_dword_splice`
is the write-side analogue of `read_word_eq_dword_extract`.
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

-- ============================================================================
-- Key lemma: byte-level word write = dword-level XOR-AND-XOR splice
-- ============================================================================

-- The XOR-AND-XOR pattern: d ^^^ ((d ^^^ v) &&& m) replaces the bits
-- selected by mask m in d with the corresponding bits from v.
-- For SW, m is a 32-bit window (0xFFFFFFFF) shifted to the correct lane.

-- Dword-aligned case (shift = 0): writing lower 4 bytes = writing 8 bytes
-- with lower half replaced.
private lemma write_word_eq_dword_splice_lower (addr : BitVec 64)
    (val : BitVec 64) (s : State)
    (h7 : addr &&& 7#64 = 0#64) :
    write_word addr (val.setWidth 32) s =
    write_dword addr
      (read_dword addr s ^^^
        ((read_dword addr s ^^^ val) &&& ((0#64 ||| (-1#64)) >>> 32)))
      s := by
  sorry

-- Word-aligned, not dword-aligned case (shift = 32): writing upper 4 bytes
-- = writing 8 bytes with upper half replaced.
private lemma write_word_eq_dword_splice_upper (addr : BitVec 64)
    (val : BitVec 64) (s : State)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    write_word addr (val.setWidth 32) s =
    write_dword (addr - 4)
      (read_dword (addr - 4) s ^^^
        ((read_dword (addr - 4) s ^^^ (val <<< 32)) &&&
         (((0#64 ||| (-1#64)) >>> 32) <<< 32)))
      s := by
  sorry

-- Combined key lemma: write_word = dword-level XOR-AND-XOR splice.
-- Analogous to read_word_eq_dword_extract from lw.lean.
lemma write_word_eq_dword_splice (addr : BitVec 64) (val : BitVec 64) (s : State)
    (h_aligned : addr &&& 3#64 = 0#64) :
    write_word addr (val.setWidth 32) s =
    (let dword_addr := addr &&& (-8#64)
     let dword := read_dword dword_addr s
     let shift := ((addr <<< 3).setWidth 6).toNat
     let mask  := ((0#64 ||| (-1#64)) >>> 32) <<< shift
     let v     := val <<< shift
     write_dword dword_addr (dword ^^^ ((dword ^^^ v) &&& mask)) s) := by
  by_cases h7 : addr &&& 7#64 = 0#64
  · -- Dword-aligned: dword_addr = addr, shift = 0
    simp only [dword_align_eq addr h7, shift_eq_zero addr h7]
    simp only [BitVec.shiftLeft_zero_eq]
    exact write_word_eq_dword_splice_lower addr val s h7
  · -- Word-aligned, not dword-aligned: dword_addr = addr - 4, shift = 32
    simp only [dword_align_sub4 addr h_aligned h7, shift_eq_32 addr h_aligned h7]
    exact write_word_eq_dword_splice_upper addr val s h_aligned h7

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem sw_eq (rs1 rs2 : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    Riscv.sw rs1 rs2 imm s = jolt_sw rs1 rs2 imm s := by
  simp only [Riscv.sw, jolt_sw, Riscv.addi, Jolt.virtualAssertWordAlignment,
             Riscv.andi, Riscv.slli, Riscv.ori, Riscv.srli,
             Riscv.sll, Riscv.xor, Riscv.and]
  by_cases h : (imm.setWidth 64 + read rs1 s.reg) &&& 3#64 = 0#64
  · -- Aligned: both sides perform the store
    simp only [ne_eq, h, not_true_eq_false, ↓reduceIte, h_no_error]
    exact write_word_eq_dword_splice _ _ s h
  · -- Misaligned: both sides panic with { s with error := true }
    simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
