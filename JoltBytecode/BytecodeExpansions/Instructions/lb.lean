import JoltBytecode.BytecodeExpansions.Instructions.Lw

/-!
# LB: RISC-V ≡ Jolt Decomposition

## Instruction (RV32I/RV64I)

`LB rd, offset(rs1)` loads a byte from memory at `rs1 + offset`,
sign-extends it to 64 bits, and writes to rd. No alignment check needed.

## Jolt Decomposition

  ADDI           v_address,    rs1,      imm
  ANDI           v_dword_addr, v_address, -8
  LD             v_dword,      v_dword_addr, 0
  XORI           v_offset,     v_address, 7
  SLLI           v_shift,      v_offset, 3
  SLL            v_shifted,    v_dword,  v_shift
  SRAI           rd,           v_shifted, 56
-/

-- ============================================================================
-- Jolt's LB decomposition
-- ============================================================================

def jolt_lb (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) : State :=
  let base              := read rs1 s.reg
  let v_address         := Riscv.addi base imm                          -- ADDI
  let v_dword_addr      := Riscv.andi v_address (-8#64)                 -- ANDI v_address, -8
  let v_dword           := read_dword v_dword_addr s                    -- LD
  let v_offset          := Riscv.xor v_address 7#64                     -- XORI v_address, 7
  let v_shift           := Riscv.slli v_offset 3                        -- SLLI v_offset, 3
  let v_shifted         := Riscv.sll v_dword v_shift                    -- SLL v_dword, v_shift
  let result            := Riscv.srai64 v_shifted 56#64                 -- SRAI v_shifted, 56
  let new_reg           := write rd result s.reg
  { s with reg := new_reg }

-- ============================================================================
-- Byte-level extraction lemmas
-- ============================================================================

-- read_dword_val expanded as 8-byte sum
lemma read_dword_val_eq_bytes (addr : BitVec 64) (s : State) :
    read_dword_val addr s =
      (read_mem addr s).toNat +
      (read_mem (addr + 1) s).toNat * 2^8 +
      (read_mem (addr + 2) s).toNat * 2^16 +
      (read_mem (addr + 3) s).toNat * 2^24 +
      (read_mem (addr + 4) s).toNat * 2^32 +
      (read_mem (addr + 5) s).toNat * 2^40 +
      (read_mem (addr + 6) s).toNat * 2^48 +
      (read_mem (addr + 7) s).toNat * 2^56 := by
  unfold read_dword_val read_word_val
  ring

-- Byte k of a dword value = (dword_val / 2^(k*8)) % 2^8
lemma extract_byte_from_dword_val (addr : BitVec 64) (s : State) (k : Nat) (hk : k < 8) :
    (read_mem (addr + BitVec.ofNat 64 k) s).toNat =
    read_dword_val addr s / 2^(k*8) % 2^8 := by
  have hb0 := (read_mem addr s).isLt
  have hb1 := (read_mem (addr + 1) s).isLt
  have hb2 := (read_mem (addr + 2) s).isLt
  have hb3 := (read_mem (addr + 3) s).isLt
  have hb4 := (read_mem (addr + 4) s).isLt
  have hb5 := (read_mem (addr + 5) s).isLt
  have hb6 := (read_mem (addr + 6) s).isLt
  have hb7 := (read_mem (addr + 7) s).isLt
  rw [read_dword_val_eq_bytes]
  interval_cases k <;> simp_all <;> omega

-- ============================================================================
-- Address arithmetic for LB
-- ============================================================================

-- The byte offset k = (addr &&& 7).toNat is < 8
lemma byte_offset_lt (addr : BitVec 64) : (addr &&& 7#64).toNat < 8 := by
  have h : addr &&& 7#64 < 8#64 := by bv_decide
  exact h

-- XOR with 7 then shift left by 3 computes (7 - byte_offset) * 8
lemma xori7_slli3_shift (addr : BitVec 64) :
    (((addr ^^^ 7#64) <<< 3).setWidth 6).toNat = (7 - (addr &&& 7#64).toNat) * 8 := by
  have h1 : ((addr ^^^ 7#64) <<< 3).setWidth 6 =
             ((7#64 - (addr &&& 7#64)) <<< 3).setWidth 6 := by bv_decide
  rw [h1]
  have hk := byte_offset_lt addr
  bv_omega

-- addr &&& -8 + addr &&& 7 = addr (bits are disjoint, so OR = ADD)
lemma addr_decompose (addr : BitVec 64) :
    (addr &&& (-8#64)) + (addr &&& 7#64) = addr := by
  bv_decide

-- ============================================================================
-- Key lemma: SLL+SRAI extracts and sign-extends a byte
-- ============================================================================

lemma sll_srai_extracts_byte (x : BitVec 64) (k : Nat) (hk : k < 8) :
    (x <<< ((7 - k) * 8)).sshiftRight 56 =
    ((x >>> (k * 8)).setWidth 8).signExtend 64 := by
  interval_cases k <;> bv_decide

-- ============================================================================
-- Bridge: byte at addr = extract from dword
-- ============================================================================

-- Round-trip: ofNat 64 (bv.toNat) = bv for BitVec 64
private lemma ofNat_toNat_64 (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

-- The byte at addr equals the corresponding byte extracted from the dword
lemma read_byte_from_dword (addr : BitVec 64) (s : State) :
    (read_mem addr s).toNat =
    read_dword_val (addr &&& (-8#64)) s / 2^((addr &&& 7#64).toNat * 8) % 2^8 := by
  have hk := byte_offset_lt addr
  have key := extract_byte_from_dword_val (addr &&& (-8#64)) s (addr &&& 7#64).toNat hk
  rw [ofNat_toNat_64, addr_decompose] at key
  exact key

-- The sign-extended byte at addr equals extracting from the dword via SLL+SRAI
lemma read_byte_eq_dword_sll_srai (addr : BitVec 64) (s : State) :
    (read_mem addr s).signExtend 64 =
    (read_dword (addr &&& (-8#64)) s <<<
      (((addr ^^^ 7#64) <<< 3).setWidth 6).toNat).sshiftRight 56 := by
  set k := (addr &&& 7#64).toNat
  have hk : k < 8 := byte_offset_lt addr
  rw [xori7_slli3_shift]
  rw [sll_srai_extracts_byte _ k hk]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
             read_dword_toNat]
  exact read_byte_from_dword addr s

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem lb_eq (rs1 rd : BitVec 5) (imm : BitVec 12) (s : State) :
    Riscv.lb rs1 rd imm s = jolt_lb rs1 rd imm s := by
  simp only [Riscv.lb, jolt_lb, Riscv.addi, Riscv.andi, Riscv.xor,
             Riscv.slli, Riscv.sll, Riscv.srai64]
  have h56 : ((56#64 : BitVec 64).setWidth 6).toNat = 56 := by native_decide
  simp only [h56]
  congr 1
  funext x
  simp only [write]
  by_cases hx : x = rd
  · simp only [hx, ↓reduceIte]
    exact read_byte_eq_dword_sll_srai (imm.setWidth 64 + read rs1 s.reg) s
  · simp [hx]
