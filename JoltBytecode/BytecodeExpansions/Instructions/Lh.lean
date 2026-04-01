/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari
-/

import JoltBytecode.BytecodeExpansions.Common.Riscv
import JoltBytecode.BytecodeExpansions.Common.Virtual
import JoltBytecode.BytecodeExpansions.Instructions.Lw

/-!
# LH: RISC-V ≡ Jolt Decomposition

## Instruction (RV32I/RV64I)

`LH rd, offset(rs1)` loads a 16-bit halfword from memory at the halfword-aligned
address `(rs1 + offset) & ~1`, sign-extends it to 64 bits, and writes to rd.

## Jolt Decomposition (64-bit, from randomwalks.xyz/Jolt-spec/isa/lh)

- VirtualAssertHalfwordAlignment(rs1, imm)
- ADDI v0, rs1, imm
- ANDI rd, v0, -8        (dword-aligned address)
- LD rd, rd, 0           (load dword)
- XORI v0, v0, 6
- SLLI v0, v0, 3         (shift amount: 0, 16, 32, or 48)
- SLL rd, rd, v0
- SRAI rd, rd, 48        (extract and sign-extend halfword)

## Proof Strategy

Halfword at addr is contained in the dword at (addr & -8). The shift (addr XOR 6) << 3
positions the halfword into the top 16 bits; SRAI 48 then sign-extends it to 64 bits.
-/

-- Jolt's LH decomposition (64-bit inline sequence).
def jolt_lh (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base               := read rs1 s.reg
  let v_address          := Riscv.addi base imm
  let (v_address, s)      := Jolt.virtualAssertHalfwordAlignment v_address s
  if s.error then s
  else
    let v_dword_addr     := Riscv.andi v_address (-8#64)
    let v_dword          := read_dword v_dword_addr s
    let v_xor            := v_address ^^^ 6#64
    let v_shift          := Riscv.slli v_xor 3
    let v_shifted        := Riscv.sll v_dword v_shift
    let result           := Riscv.srai64 v_shifted 48#64
    let new_reg          := write rd result s.reg
    { s with reg := new_reg }

-- ============================================================================
-- Nat-level bounds and extraction
-- ============================================================================

lemma read_halfword_val_lt (addr : BitVec 64) (s : State) :
    read_halfword_val addr s < 2^16 := by
  unfold read_halfword_val
  have := (read_mem addr s).isLt
  have := (read_mem (addr + 1) s).isLt
  omega

-- ============================================================================
-- Bridge: BitVec ↔ Nat for halfword
-- ============================================================================

lemma read_halfword_toNat (addr : BitVec 64) (s : State) :
    (read_halfword addr s).toNat = read_halfword_val addr s := by
  unfold read_halfword; rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (read_halfword_val_lt addr s)

-- For shift in {0,16,32,48}, ((x <<< shift).sshiftRight 48).toNat % 2^16 extracts the right 16-bit half.
private lemma sll_sra48_mod16_48 (x : BitVec 64) :
    ((x <<< 48).sshiftRight 48).toNat % 2^16 = x.toNat % 2^16 := by sorry
private lemma sll_sra48_mod16_32 (x : BitVec 64) :
    ((x <<< 32).sshiftRight 48).toNat % 2^16 = (x.toNat / 2^16) % 2^16 := by sorry
private lemma sll_sra48_mod16_16 (x : BitVec 64) :
    ((x <<< 16).sshiftRight 48).toNat % 2^16 = (x.toNat / 2^32) % 2^16 := by sorry
private lemma sll_sra48_mod16_0 (x : BitVec 64) :
    ((x <<< 0).sshiftRight 48).toNat % 2^16 = (x.toNat / 2^48) % 2^16 := by sorry

-- ============================================================================
-- Key lemma: halfword read = extract from dword (Jolt sequence)
-- ============================================================================
-- For halfword-aligned addr, the value (read_halfword addr s).signExtend 64
-- equals (read_dword (addr &&& -8) s <<< shift).sshiftRight 48
-- where shift = ((addr ^^^ 6#64) <<< 3).setWidth 6).toNat (0, 16, 32, or 48).
-- We prove the 16-bit values agree, then (x.setWidth 16).signExtend 64 = x for the RHS.
lemma read_halfword_eq_dword_extract (addr : BitVec 64) (s : State)
    (h_aligned : addr &&& 1#64 = 0#64) :
    (read_halfword addr s).signExtend 64 =
    (read_dword (addr &&& (-8#64)) s <<<
      (((addr ^^^ 6#64) <<< 3).setWidth 6).toNat).sshiftRight 48 := by
  sorry
  -- TODO: Prove by showing RHS = (RHS.setWidth 16).signExtend 64, then 16-bit value equality.
  -- Case split on addr & 7 ∈ {0,2,4,6}; use sll_sra48_mod16_* and read_dword_toNat; omega.

-- ============================================================================
-- Main theorem
-- ============================================================================
theorem lh_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State)
    (h_no_error : s.error = false) :
    Riscv.lh rs1 rd imm s = jolt_lh rs1 rd imm s := by
  simp only [Riscv.lh, jolt_lh, Riscv.addi, Jolt.virtualAssertHalfwordAlignment,
             Riscv.andi, Riscv.slli, Riscv.sll, Riscv.srai64]
  by_cases h : (imm.setWidth 64 + read rs1 s.reg) &&& 1#64 = 0#64
  · simp only [ne_eq, h, not_true_eq_false, ↓reduceIte, h_no_error]
    congr 1
    funext x
    simp only [write]
    by_cases hx : x = rd
    · simp only [hx, ↓reduceIte]
      exact read_halfword_eq_dword_extract (imm.setWidth 64 + read rs1 s.reg) s h
    · simp [hx]
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
