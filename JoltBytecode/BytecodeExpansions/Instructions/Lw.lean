/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual

-- Helper: extract mod from &&& mask = 0
private lemma and_mask_eq_zero_imp_mod (addr : BitVec 64) (k : Nat) (mask : Nat)
    (hmask : mask = 2^k - 1) (hmod : mask % 2^64 = mask)
    (h : addr &&& BitVec.ofNat 64 mask = 0) : addr.toNat % 2^k = 0 := by
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, hmod, hmask,
      Nat.and_two_pow_sub_one_eq_mod] at h'
  simpa using h'

-- Helper: if x &&& y = 0 then x &&& ~~~y = x
private lemma and_compl_of_and_eq_zero {w : Nat} (x y : BitVec w) (h : x &&& y = 0) :
    x &&& ~~~y = x := by
  have : x = (x &&& y) ||| (x &&& ~~~y) := by
    rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
  rw [h] at this; simp at this; exact this.symm

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

lemma read_word_val_lt (addr : BitVec 64) (s : State) :
    read_word_val addr s < 2^32 := by
  unfold read_word_val
  have := (read_mem addr s).isLt
  have := (read_mem (addr + 1) s).isLt
  have := (read_mem (addr + 2) s).isLt
  have := (read_mem (addr + 3) s).isLt
  omega

lemma read_dword_val_lt (addr : BitVec 64) (s : State) :
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

lemma read_word_toNat (addr : BitVec 64) (s : State) :
    (read_word addr s).toNat = read_word_val addr s := by
  unfold read_word; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_word_val_lt addr s)

lemma read_dword_toNat (addr : BitVec 64) (s : State) :
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
lemma dword_align_eq (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) : addr &&& (-8#64) = addr := by
  rw [show (-8#64 : BitVec 64) = ~~~(7#64) from by native_decide]
  exact and_compl_of_and_eq_zero addr 7#64 h

-- Not dword-aligned: addr &&& -8 = addr - 4 when addr &&& 3 = 0 and addr &&& 7 ≠ 0
lemma dword_align_sub4 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    addr &&& (-8#64) = addr - 4 := by
  -- addr &&& 7 must be 4 (mod 4 = 0 but mod 8 ≠ 0)
  have h4 : addr &&& 7#64 = 4#64 := by
    have hlow : (addr &&& 7#64) &&& 3#64 = 0#64 := by
      rw [BitVec.and_assoc, show (7#64 : BitVec 64) &&& 3#64 = 3#64 from by native_decide]; exact h3
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_and, BitVec.toNat_ofNat]; norm_num
    have hmod4 := congrArg BitVec.toNat hlow
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at hmod4; norm_num at hmod4
    rw [show (3:Nat) = 2^2 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod] at hmod4
    have hne : addr.toNat &&& 7 ≠ 0 := by
      intro h0; exact h7 (BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_and, BitVec.toNat_ofNat]; exact h0))
    have hlt : addr.toNat &&& 7 < 8 := by
      rw [show (7:Nat) = 2^3 - 1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]; omega
    omega
  rw [show (-8#64 : BitVec 64) = ~~~(7#64) from by native_decide]
  have split : addr = (addr &&& 7#64) ||| (addr &&& ~~~7#64) := by
    rw [← BitVec.and_or_distrib_left, BitVec.or_not_self, BitVec.and_allOnes]
  rw [h4] at split
  have disj : 4#64 &&& (addr &&& ~~~7#64) = 0 := by
    rw [BitVec.and_comm, BitVec.and_assoc,
        show ~~~(7#64 : BitVec 64) &&& 4#64 = 0 from by native_decide]; simp
  rw [(BitVec.add_eq_or_of_and_eq_zero 4#64 (addr &&& ~~~7#64) disj).symm] at split
  bv_omega

-- Shift = 0 when dword-aligned
lemma shift_eq_zero (addr : BitVec 64)
    (h : addr &&& 7#64 = 0#64) :
    ((addr <<< 3).setWidth 6).toNat = 0 := by
  have h7 := and_mask_eq_zero_imp_mod addr 3 7 (by norm_num) (by norm_num) h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := addr.isLt; omega

-- Shift = 32 when word-aligned but not dword-aligned
lemma shift_eq_32 (addr : BitVec 64)
    (h3 : addr &&& 3#64 = 0#64) (h7 : ¬(addr &&& 7#64 = 0#64)) :
    ((addr <<< 3).setWidth 6).toNat = 32 := by
  have hmod4 := and_mask_eq_zero_imp_mod addr 2 3 (by norm_num) (by norm_num) h3
  have hmod8 : addr.toNat % 8 ≠ 0 := by
    intro heq; apply h7; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]; norm_num
    rwa [show (7:Nat) = 2^3-1 from by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := addr.isLt; omega

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
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [pow_zero, Nat.div_one, read_dword_toNat, read_word_toNat]
    exact extract_lower_word addr s
  · -- Word-aligned, not dword-aligned: dword_addr = addr - 4, shift = 32
    rw [dword_align_sub4 addr h_aligned h7, shift_eq_32 addr h_aligned h7]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
        read_dword_toNat, read_word_toNat]
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
    · funext x
      simp only [write]
      by_cases hx : x = rd
      · simp only [hx, ↓reduceIte]
        congr
        exact read_word_eq_dword_extract _ s h
      · simp [hx]
  · -- Misaligned: both sides panic with { s with error := true }
    simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]

