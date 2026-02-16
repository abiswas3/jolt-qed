import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual

/-!
# LW: RISC-V ≡ Jolt Decomposition

## Instruction (RV32I/RV64I)

`LW rd, offset(rs1)` loads a 32-bit word from memory at the word-aligned
address `(rs1 + offset) & ~3`, sign-extends it to 64 bits, and writes to rd.

## Jolt Decomposition

Jolt reads a 64-bit dword from the dword-aligned address, shifts to extract
the 32-bit word, then sign-extends.

## Proof Strategy

Define `read_word_val` and `read_dword_val` as Nat-valued little-endian
byte sums. The dword is just two words: `dword = lo_word + hi_word * 2^32`.
Extraction is then pure Nat arithmetic (mod/div by 2^32), handled by omega.
-/

-- Nat value of 8 little-endian bytes at addr = two consecutive words.
def read_dword_val (addr : BitVec 64) (s : State) : Nat :=
  read_word_val addr s + read_word_val (addr + 4) s * 2^32

-- BitVec wrapper: read a 64-bit dword from memory.
def read_dword (addr : BitVec 64) (s : State) : BitVec 64 :=
  BitVec.ofNat 64 (read_dword_val addr s)

-- Jolt's LW decomposition: sequence of RISC-V and virtual instructions.
-- Mirrors the Jolt Rust expansion:
--   VirtualAssertWordAlignment  rs1, imm
--   ADDI           v_address,      rs1,    imm
--   ANDI           v_dword_addr,   v_address, -8
--   LD             v_dword,        v_dword_addr, 0
--   SLLI           v_shift,        v_address, 3
--   SRL            rd,             v_dword, v_shift
--   VirtualSignExtendWord rd,      rd, 0
def jolt_lw (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base              := read rs1 s.reg
  let v_address         := Riscv.addi base imm                          -- ADDI v_address, rs1, imm
  let (v_address, s)    := Jolt.virtualAssertWordAlignment v_address s  -- VirtualAssertWordAlignment
  if s.error then s                                                     -- panic: early exit
  else
    let v_dword_addr    := Riscv.andi v_address (-8#64)                -- ANDI v_dword_addr, v_address, -8
    let v_dword         := read_dword v_dword_addr s                   -- LD v_dword, v_dword_addr, 0
    let v_shift         := Riscv.slli v_address 3                      -- SLLI v_shift, v_address, 3
    let v_word          := Riscv.srl v_dword v_shift                   -- SRL rd, v_dword, v_shift
    let result          := Jolt.virtualSignExtendWord v_word            -- VirtualSignExtendWord rd, rd, 0
    let new_reg         := write rd result s.reg
    { s with reg := new_reg }

-- ============================================================================
-- Nat-level bounds and extraction lemmas
-- ============================================================================

private lemma read_word_val_lt (addr : BitVec 64) (s : State) :
    read_word_val addr s < 2^32 := by
  unfold read_word_val
  have := (read_mem addr s).isLt
  have := (read_mem (addr + 1) s).isLt
  have := (read_mem (addr + 2) s).isLt
  have := (read_mem (addr + 3) s).isLt
  omega

private lemma read_dword_val_lt (addr : BitVec 64) (s : State) :
    read_dword_val addr s < 2^64 := by
  unfold read_dword_val
  have := read_word_val_lt addr s
  have := read_word_val_lt (addr + 4) s
  omega

-- Lower word of dword (shift = 0 case).
private lemma extract_lower_word (addr : BitVec 64) (s : State) :
    read_word_val addr s = read_dword_val addr s % 2^32 := by
  unfold read_dword_val
  have := read_word_val_lt addr s
  omega

-- Upper word of dword (shift = 32 case).
-- lo_addr + 4 = hi_addr (the word we want is the upper half of the dword).
private lemma extract_upper_word (lo hi : BitVec 64) (s : State)
    (h : lo + 4 = hi) :
    read_word_val hi s = read_dword_val lo s / 2^32 % 2^32 := by
  unfold read_dword_val; rw [h]
  have := read_word_val_lt lo s
  have := read_word_val_lt hi s
  omega

-- ============================================================================
-- Bridge lemmas: BitVec ↔ Nat
-- ============================================================================

private lemma read_word_toNat (addr : BitVec 64) (s : State) :
    (read_word addr s).toNat = read_word_val addr s := by
  unfold read_word; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_word_val_lt addr s)

private lemma read_dword_toNat (addr : BitVec 64) (s : State) :
    (read_dword addr s).toNat = read_dword_val addr s := by
  unfold read_dword; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_dword_val_lt addr s)

-- ============================================================================
-- Address arithmetic
-- ============================================================================

-- (x &&& -4) &&& 3 = 0
private lemma and_neg4_and_3_eq_0 (x : BitVec 64) :
    (x &&& (-4#64)) &&& 3#64 = 0#64 := by
  have : (-4#64) &&& 3#64 = 0#64 := by native_decide
  rw [BitVec.and_assoc]; simp [this]

-- Dword-aligned: addr &&& -8 = addr when addr &&& 7 = 0
private lemma dword_align_eq (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) : addr &&& (-8#64) = addr := by
  bv_decide

-- Not dword-aligned: addr &&& -8 = addr - 4 when addr &&& 3 = 0 and addr &&& 7 ≠ 0
private lemma dword_align_sub4 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    addr &&& (-8#64) = addr - 4 := by
  bv_decide

-- Shift = 0 when dword-aligned
private lemma shift_eq_zero (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) :
    ((addr <<< 3).setWidth 6).toNat = 0 := by
  have : (addr <<< 3).setWidth 6 = 0#6 := by bv_decide
  simp [this]

-- Shift = 32 when word-aligned but not dword-aligned
private lemma shift_eq_32 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    ((addr <<< 3).setWidth 6).toNat = 32 := by
  have : (addr <<< 3).setWidth 6 = 32#6 := by bv_decide
  simp [this]

-- ============================================================================
-- Key lemma: word read = extract from dword (via Nat bridge)
-- ============================================================================

lemma read_word_eq_dword_extract (addr : BitVec 64) (s : State)
    (h_aligned : addr &&& 3#64 = 0#64) :
    read_word addr s =
    (read_dword (addr &&& (-8#64)) s >>> ((addr <<< 3).setWidth 6).toNat).setWidth 32 := by
  -- Rewrite address/shift in BitVec land FIRST, then convert to Nat.
  by_cases h7 : addr &&& 7#64 = 0#64
  · -- Dword-aligned: dword_addr = addr, shift = 0
    rw [dword_align_eq addr h7, shift_eq_zero addr h7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
               Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one,
               read_dword_toNat, read_word_toNat]
    exact extract_lower_word addr s
  · -- Word-aligned, not dword-aligned: dword_addr = addr - 4, shift = 32
    rw [dword_align_sub4 addr h_aligned h7, shift_eq_32 addr h_aligned h7]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
               Nat.shiftRight_eq_div_pow, read_dword_toNat, read_word_toNat]
    have h_addr : addr - 4 + 4 = addr := by bv_omega
    exact extract_upper_word (addr - 4) addr s h_addr

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem lw_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    Riscv.lw rs1 rd imm s = jolt_lw rs1 rd imm s := by
  simp only [Riscv.lw, jolt_lw, Riscv.addi, Jolt.virtualAssertWordAlignment,
             Riscv.andi, Riscv.slli, Riscv.srl, Jolt.virtualSignExtendWord]
  by_cases h : (imm.setWidth 64 + read rs1 s.reg) &&& 3#64 = 0#64
  · -- Aligned: both sides perform the load
    simp only [ne_eq, h, not_true_eq_false, ↓reduceIte, h_no_error]
    congr 1
    funext x
    simp only [write]
    by_cases hx : x = rd
    · simp only [hx, ↓reduceIte]
      congr 1
      exact read_word_eq_dword_extract _ s h
    · simp [hx]
  · -- Misaligned: both sides panic with { s with error := true }
    simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
